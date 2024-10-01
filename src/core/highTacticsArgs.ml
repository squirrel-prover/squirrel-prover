include TacticsArgs

module Sv = Vars.Sv

(*------------------------------------------------------------------*)
let as_p_path parser_args =
  match parser_args with
  | [Theory (L.{ pl_desc = Symb (p, None) } )] ->
    Some p
  | _ -> None

(*------------------------------------------------------------------*)
let convert_pat_arg
    (sel : int) conv_cntxt (p : Typing.term) (conc : Equiv.any_form)
  =
  let t, ty = Typing.convert ~pat:true conv_cntxt p in

  let pat = Pattern.op_pat_of_term t in
  
  let option = { Match.default_match_option with allow_capture = true; } in
  let table = conv_cntxt.env.table
  and system = conv_cntxt.env.system in
  let res : Term.terms = 
    match conc with
    | Local  form -> Match.T.find ~option table system pat form
    | Global form -> Match.E.find ~option table system pat form
  in
  let res =
    (* Clear terms whose free free variables are not a subset of the context free
       variables (because the term appeared under a binder). *)
    List.filter (fun t ->
        Sv.subset (Term.fv t) (Vars.to_vars_set conv_cntxt.env.vars)
      ) res
  in
  let message = match List.nth_opt res (sel-1) with
    | Some et -> et
    | None -> 
      raise Typing.(Error (L._dummy,
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
    | [Theory p], Sort Timestamp ->
      let f, _ = Typing.convert conv_cntxt ~ty:Type.ttimestamp p in
      Arg (Message (f, Type.ttimestamp))

    | [TermPat (sel, p)], Sort Message ->
      let (m, ty) = convert_pat_arg sel conv_cntxt p conc in
      Arg (Message (m, ty))

    | [Theory p], Sort Message ->
      begin match Typing.convert conv_cntxt p with
        | (t, ty) -> Arg (Message (t, ty))
        | exception Typing.(Error (_,PatNotAllowed)) ->
          let (m, ty) = convert_pat_arg 1 conv_cntxt p conc in
          Arg (Message (m, ty))
      end

    | [Theory p], Sort Boolean ->
      let f, _ = Typing.convert conv_cntxt ~ty:Type.tboolean p in
      Arg (Message (f, Type.tboolean))

    | [Theory p], Sort Term ->
      let et = 
        try
          let et, ty = Typing.convert conv_cntxt p in
          Term (ty,et,L.loc p)
        with Typing.(Error (_,PatNotAllowed)) ->
          let (m,ty) = convert_pat_arg 1 conv_cntxt p conc in
          Term (ty, m, L.loc p)
      in
      Arg et

    | [Theory (L.{ pl_desc = Symb (([],p), None) } )], Sort String ->
      Arg (String p)

    | [Int_parsed i], Sort Int ->
      Arg (Int i)

    | [Theory t], Sort String ->
      raise Typing.(Error (L.loc t, Failure "expected a string"))

    | [Theory t], Sort Int ->
      raise Typing.(Error (L.loc t, Failure "expected an integer"))

    | [Theory p], Sort Index ->
      let f = 
        match Typing.convert conv_cntxt ~ty:Type.tindex p with
        | Term.Var v, _ -> v
        | _ -> Typing.conv_err (L.loc p) (Failure "must be a variable of type index")
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
