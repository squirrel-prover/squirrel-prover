open Utils
    
include TacticsArgs

module Sv = Vars.Sv

(*------------------------------------------------------------------*)
let as_p_path (parser_args : parser_arg list) : Symbols.p_path option =
  match parser_args with
  | [Term_parsed (L.{ pl_desc = Symb { path = p; ty_args = None; se_args = None; }} )] ->
    Some p
  | _ -> None

(*------------------------------------------------------------------*)
(** Exported, see `.mli` *)
let occurrences_of_pat
    ?(ienv : Infer.env option) ?(in_system : SE.t option)
    (env : Env.t)
    (pat : Term.t) ~(target : Equiv.any_form)
  : Term.t list
  =
  let ienv = match ienv with None -> Infer.mk_env () | Some ienv -> ienv in

  let pat = Pattern.op_pat_of_term pat in
  
  let param = { Match.default_param with allow_capture = true; } in
  let res : Term.terms = 
    match target with
    | Local  form -> Match.T.find ~param ?in_system ~ienv env.table env.system pat form
    | Global form -> Match.E.find ~param ?in_system ~ienv env.table env.system pat form
  in

  (* close [ienv] if at least one match was found *)
  let res =
    if res = [] then [] else
      match Infer.close env ienv with
      | Infer.Closed s -> List.map (Term.gsubst s) res
      | _ -> assert false
      (* Since [res ≠ []], we know that we successfully matched [pat].
         Thus, no free type variable may remain. *)
  in

  (* Clear terms whose free free variables are not a subset of the context free
     variables (because the term appeared under a binder). *)
  List.filter (fun t ->
      Sv.subset (Term.fv t) (Vars.to_vars_set env.vars)
    ) res


(*------------------------------------------------------------------*)
let convert_pat_arg
    (sel : int) conv_cntxt (p : Typing.term) (conc : Equiv.any_form)
  =
  let ienv = Infer.mk_env () in
  let t, ty =
    Typing.convert
      ~option:{Typing.Option.default with pat = true; }
      conv_cntxt ~ienv p
  in
  let res = occurrences_of_pat ~ienv conv_cntxt.env t ~target:conc in
  let message =
    match List.nth_opt res (sel-1) with
    | Some et -> et
    | None -> 
      raise Typing.(Error (L.loc p,
                           Tactic_type
                             ("Could not extract the element "
                              ^ string_of_int (sel)
                              ^ " out of " ^ string_of_int (List.length res)
                              ^ " matches found")))
  in
  (message, ty)

(*------------------------------------------------------------------*)
let convert_args env parser_args tactic_type conc =
  let conv_cntxt = Typing.{ env; cntxt = InGoal; } in

  let rec conv_args parser_args tactic_type =
    match parser_args, tactic_type with
    | [Term_parsed p], Sort Timestamp ->
      let f, _ = Typing.convert conv_cntxt ~ty:Type.ttimestamp p in
      Arg (Message (f, Type.ttimestamp))

    | [TermPat (sel, p)], Sort Message ->
      let (m, ty) = convert_pat_arg sel conv_cntxt p conc in
      Arg (Message (m, ty))

    | [Term_parsed p], Sort Message ->
      begin match Typing.convert conv_cntxt p with
        | (t, ty) -> Arg (Message (t, ty))
        | exception Typing.(Error (_,PatNotAllowed)) ->
          let (m, ty) = convert_pat_arg 1 conv_cntxt p conc in
          Arg (Message (m, ty))
      end

    | [Term_parsed p], Sort Boolean ->
      let f, _ = Typing.convert conv_cntxt ~ty:Type.tboolean p in
      Arg (Message (f, Type.tboolean))

    | [Term_parsed p], Sort Term ->
      let et = 
        try
          let et, ty = Typing.convert conv_cntxt p in
          Term (ty,et,L.loc p)
        with Typing.(Error (_,PatNotAllowed)) ->
          let (m,ty) = convert_pat_arg 1 conv_cntxt p conc in
          Term (ty, m, L.loc p)
      in
      Arg et

    | [Term_parsed (L.{ pl_desc = Symb ({ path = ([],p) } as symb)} )], Sort String
      when symb.ty_args = None && symb.se_args = None 
      ->
      Arg (String p)

    | [Term_parsed L.{ pl_desc = Int i }], Sort Int ->
      Arg (Int i)

    | [Int_parsed i], Sort Int ->
      Arg (Int i)

    | [Term_parsed t], Sort String ->
      raise Typing.(Error (L.loc t, Failure "expected a string"))

    | [Term_parsed t], Sort Int ->
      raise Typing.(Error (L.loc t, Failure "expected an integer"))

    | [Term_parsed p], Sort Index ->
      let f = 
        match Typing.convert conv_cntxt ~ty:Type.tindex p with
        | Term.Var v, _ -> v
        | _ -> Typing.error (L.loc p) (Failure "must be a variable of type index")
      in
      Arg (Index (f))

    | th1::q, Sort (Pair (Opt s1, s2)) ->
      begin match conv_args [th1] (Sort (Opt s1)) with
        | Arg arg1 ->
          let Arg arg2 = conv_args q (Sort s2) in
          Arg (Pair (arg1, arg2))
        | exception Typing.(Error _) ->
          let Arg arg2 = conv_args (th1::q) (Sort s2) in
          Arg (Pair (Opt (s1, None), arg2))
      end

    | th1::q, Sort (Pair (s1, s2)) ->
      let Arg arg1 = conv_args [th1] (Sort s1) in
      let Arg arg2 = conv_args q (Sort s2) in
      Arg (Pair (arg1, arg2))

    | [], Sort (Opt a) ->
      Arg (Opt (a, None))

    | [], Sort (Pair (Opt a, b)) ->
      let Arg arg2 = conv_args [] (Sort b) in
      Arg (Pair (Opt (a, None), arg2))

    | [th], Sort (Opt a) ->
      let Arg arg = conv_args [th] (Sort a) in
      Arg (Opt
             (a,
              (Some (cast a arg))
             )
          )

    | [], Sort None -> Arg None

    | [], _ -> raise Typing.(Error (L._dummy, Tactic_type "more arguments expected"))

    | _ :: _, _  ->
      raise Typing.(Error (L._dummy,
                          Tactic_type "tactic argument error \
                                       (maybe you gave too many arguments?)"))

  in
  conv_args parser_args tactic_type 
