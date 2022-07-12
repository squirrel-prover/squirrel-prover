(*------------------------------------------------------------------*)
include TacticsArgs


(*------------------------------------------------------------------*)
let convert_as_lsymb parser_args = match parser_args with
  | [Theory (L.{ pl_desc = App (p,[]) } )] ->
    Some p
  | _ -> None

(*------------------------------------------------------------------*)
let convert_pat_arg sel conv_cntxt p (conc : Equiv.any_form) =
  let t, ty = Theory.convert ~pat:true conv_cntxt p in
  let pat_vars =
    Vars.Sv.filter (fun v -> Vars.is_pat v) (Term.fv t)
  in
  let pat = Term.{
      pat_tyvars = [];
      pat_vars;
      pat_term = t; }
  in
  let option = { Match.default_match_option with allow_capture = true; } in
  let table = conv_cntxt.env.table
  and system = conv_cntxt.env.system
  and vars  = conv_cntxt.env.vars in
  let res = match conc with
    | Local form -> Match.T.find ~option table system vars pat form
    | Global form -> Match.E.find ~option table system vars pat form
  in
  let message = match List.nth res (sel-1) with
    | et -> et
    | exception _ -> 
      raise Theory.(Conv (L._dummy,
                          Tactic_type
                            ("Could not extract the element "
                             ^ string_of_int (sel)
                             ^ " out of " ^ string_of_int (List.length res)
                             ^ " matches found")))
  in
  (message, ty)

(*------------------------------------------------------------------*)
let convert_args env parser_args tactic_type conc =
  let conv_cntxt = Theory.{ env; cntxt = InGoal; } in

  let rec conv_args parser_args tactic_type =
    match parser_args, tactic_type with
    | [Theory p], Sort Timestamp ->
      let f, _ = Theory.convert conv_cntxt ~ty:Type.Timestamp p in
      Arg (Message (f, Type.Timestamp))

    | [TermPat (sel, p)], Sort Message ->
      let (m, ty) = convert_pat_arg sel conv_cntxt p conc in
      Arg (Message (m, ty))

    | [Theory p], Sort Message ->
      begin match Theory.convert conv_cntxt p with
        | (t, ty) -> Arg (Message (t, ty))
        | exception Theory.(Conv (_,PatNotAllowed)) ->
          let (m, ty) = convert_pat_arg 1 conv_cntxt p conc in
          Arg (Message (m, ty))
      end
    | [Theory p], Sort Boolean ->
      let f, _ = Theory.convert conv_cntxt ~ty:Type.Boolean p in
      Arg (Message (f, Type.Boolean))

    | [Theory p], Sort Term ->
      let et = 
        try
          let et, ty = Theory.convert conv_cntxt p in
          Term (ty,et,L.loc p)
        with Theory.(Conv (_,PatNotAllowed)) ->
          let (m,ty) = convert_pat_arg 1 conv_cntxt p conc in
          Term (ty, m, L.loc p)
      in
      Arg et

    | [Theory (L.{ pl_desc = App (p,[]) } )], Sort String ->
      Arg (String p)

    | [Int_parsed i], Sort Int ->
      Arg (Int i)

    | [Theory t], Sort String ->
      raise Theory.(Conv (L.loc t, String_expected (L.unloc t)))

    | [Theory t], Sort Int ->
      raise Theory.(Conv (L.loc t, Int_expected (L.unloc t)))

    | [Theory p], Sort Index ->
      let f = 
        match Theory.convert conv_cntxt ~ty:Type.Index p with
        | Term.Var v, _ -> v
        | _ -> Theory.conv_err (L.loc p) NotVar
      in
      Arg (Index (f))

    | th1::q, Sort (Pair (Opt s1, s2)) ->
      begin match conv_args [th1] (Sort (Opt s1)) with
        | Arg arg1 ->
          let Arg arg2 = conv_args q (Sort s2) in
          Arg (Pair (arg1, arg2))
        | exception Theory.(Conv _) ->
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

    | [], _ -> raise Theory.(Conv (L._dummy, Tactic_type "more arguments expected"))

    | p :: _, _  ->
      raise Theory.(Conv (L._dummy,
                          Tactic_type "tactic argument error \
                                       (maybe you gave too many arguments?)"))

  in
  conv_args parser_args tactic_type 
