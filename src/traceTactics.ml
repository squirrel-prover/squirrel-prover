(** All reachability tactics.
   Tactics are organized in three classes:
    - Logical -> relies on the logical properties of the sequent.
    - Strucutral -> relies on properties of protocols, or of equality over messages,...
    - Cryptographic -> relies on a cryptographic assumptions, that must be assumed.*)

open Term
open Utils

module T = Prover.TraceTactics
module Args = TacticsArgs
module L = Location
module SE = SystemExpr

open LowTactics

module TS = TraceSequent

module Hyps = TS.Hyps

type tac = TS.t Tactics.tac
type lsymb = Theory.lsymb
type sequent = TS.sequent

module LT = LowTactics.LowTac(TraceSequent)

(*------------------------------------------------------------------*)
(** {2 Logical Tactics} *)

(** Propositional connectives *)

let goal_or_right_1 (s : TS.t) =
  match Term.destr_or (TS.goal s) with
  | Some (lformula, _) -> [TS.set_goal (lformula) s]
  | None -> soft_failure (Tactics.Failure "not a disjunction")

let goal_or_right_2 (s : TS.t) =
  match Term.destr_or (TS.goal s) with
  | Some (_, rformula) -> [TS.set_goal (rformula) s]
  | None -> soft_failure (Tactics.Failure "not a disjunction")

let () =
  T.register "left"
    ~tactic_help:{general_help = "Reduce a goal with a disjunction conclusion \
                                  into the goal where the conclusion has been \
                                  replaced with the first disjunct.";
                  detailed_help = "G => A v B yields G => A";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    goal_or_right_1;

  T.register "right"
    ~tactic_help:{general_help = "Reduce a goal with a disjunction conclusion \
                                  into the goal where the conclusion has been \
                                  replace with the second disjunct.";
                  detailed_help = "G => A v B yields G => B";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    goal_or_right_2

(*------------------------------------------------------------------*)
let goal_true_intro (s : TS.t) =
  match TS.goal s with
  | tt when tt = Term.mk_true -> []
  | _ -> soft_failure (Tactics.Failure "Cannot introduce true")

let () =
  T.register "true"
     ~tactic_help:{general_help = "Solves a goal when the conclusion is true.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    goal_true_intro

(*------------------------------------------------------------------*)
let print_tac s =
  Tactics.print_system (TS.table s) (TS.system s);
  [s]

let () =
  T.register "print"
    ~tactic_help:{general_help = "Shows the current system.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    print_tac

(*------------------------------------------------------------------*)
(** Split a conjunction conclusion,
  * creating one subgoal per conjunct. *)
let goal_and_right (s : TS.t) =
  match Term.destr_and (TS.goal s) with
  | Some (lformula, rformula) ->
    [ TS.set_goal lformula s ;
      TS.set_goal rformula s ]
  | None -> soft_failure (Tactics.Failure "not a conjunction")

let () =
  T.register "split"
    ~tactic_help:{general_help = "Split a conjunction conclusion, creating one \
                                  subgoal per conjunct.";
                  detailed_help = "G=> A & B is replaced by G=>A and goal G=>B.";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    goal_and_right


(*------------------------------------------------------------------*)
let left_not_intro (Args.String hyp_name) s =
  let id, formula = Hyps.by_name hyp_name s in
  let s = Hyps.remove id s in
  match Term.destr_not formula with
  | Some f ->
    [Hyps.add (Args.Named (Ident.name id)) (Term.not_simpl f) s]

  | None -> soft_failure (Tactics.Failure "cannot introduce negation")

let () =
  T.register_typed "notleft"
    ~general_help:"Push a negation inside a formula."
    ~detailed_help:"Normalize the formula according to the negation rules over \
                    logical connectors."
    ~tactic_group:Logical
    left_not_intro Args.String

(*------------------------------------------------------------------*)
let expand_tac args s =
    let args = List.map (function
        | Args.Theory t -> t
        | _ -> bad_args ()
      ) args
    in
    [LT.expands args s]

let expand_tac args = LT.wrap_fail (expand_tac args)

let () = T.register_general "expand"
    ~tactic_help:{
      general_help  = "Expand all occurences of the given macro inside the \
                       goal.";
      detailed_help = "Can only be called over macros with fully defined \
                       timestamps.";
      tactic_group  = Structural;
      usages_sorts  = [Sort Args.String; Sort Args.Message; Sort Args.Boolean]; }
    expand_tac

(*------------------------------------------------------------------*)
(* cannot fail, so we don't need to catch soft errors *)
let () = T.register "expandall"
    ~tactic_help:{
      general_help  = "Expand all possible macros in the sequent.";
      detailed_help = "";
      tactic_group  = Structural;
      usages_sorts  = []; }
    (LT.expand_all_l `All)         (* FIXME: allow user to specify targets *)


(*------------------------------------------------------------------*)
(** Apply a naming pattern to a variable or hypothesis. *)
let do_naming_pat (ip_handler : Args.ip_handler) n_ip s : sequent =
  match ip_handler with
  | `Var Vars.EVar v ->
    let env, v' = 
      LT.var_of_naming_pat n_ip ~dflt_name:(Vars.name v) (Vars.ty v) (TS.env s)
    in
    let subst = [Term.ESubst (Term.Var v, Term.Var v')] in

    (* FIXME: we substitute everywhere. This is inefficient. *)
    TS.subst subst (TS.set_env env s)

  | `Hyp hid ->
    let f = Hyps.by_id hid s in
    let s = Hyps.remove hid s in

    Hyps.add n_ip f s

(*------------------------------------------------------------------*)
let () =
  T.register_general "revert"
    ~tactic_help:{
      general_help = "Take an hypothesis H, and turns the conclusion C into the \
                      implication H => C.";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    LT.revert_tac

(*------------------------------------------------------------------*)
(** Case analysis on [orig = Find (vars,c,t,e)] in [s].
  * This can be used with [vars = []] if orig is an [if-then-else] term. *)
let case_cond orig vars c t e s : sequent list =
  let env = ref (TS.env s) in
  let vars' = List.map (Vars.fresh_r env) vars in
  let subst =
    List.map2
      (fun i i' -> ESubst (Term.Var i, Term.Var i'))
      vars vars'
  in
  let then_c = Term.subst subst c in
  let else_c =
    Term.mk_forall (List.map (fun i -> Vars.EVar i) vars) (Term.mk_not c)
  in

  let then_t = Term.subst subst t in
  let else_t = e in

  let mk_case case_vars case_t case_cond : sequent =
    let case_subst =
      if case_vars = [] then [Term.ESubst (orig, case_t)] else []
    in

    let prem =
      Term.mk_exists
        (List.map (fun x -> Vars.EVar x) case_vars)
        (Term.mk_and ~simpl:false
           case_cond
           (Term.Atom (`Message (`Eq, orig, case_t))))
    in

    let case_goal =
      Term.mk_impl ~simpl:false
        prem
        (Term.subst case_subst (TS.goal s))
    in
    TS.set_goal case_goal s
  in

  [ mk_case vars' then_t then_c;
    mk_case    [] else_t else_c]

let conditional_case (m : Term.message) s : sequent list =
  match m with
  | Term.Find (vars,c,t,e) -> case_cond m vars c t e s
  | Term.Fun (f,_,[c;t;e]) when f = Term.f_ite ->
    case_cond m [] c t e s

  | Term.Macro (ms,[],ts)
    when Macros.is_defined ms.s_symb ts (TS.table s) ->

    if not (TS.query_happens ~precise:true s ts) then
      soft_failure (Tactics.MustHappen ts);


    begin
      match Macros.get_definition (TS.mk_trace_cntxt s) ms ts with
      | Term.Find (vars,c,t,e) -> case_cond m vars c t e s
      | Term.Fun (f,_,[c;t;e]) when f = Term.f_ite -> case_cond m [] c t e s
      | _ -> Tactics.(soft_failure (Failure "message is not a conditional"))
    end

  | _ ->
    Tactics.(soft_failure (Failure "message is not a conditional"))

let boolean_case b s : sequent list =
  let do_one b_case b_val =
    let g = Term.subst [Term.ESubst (b, b_val)] (TS.goal s) in
    TS.set_goal (Term.mk_impl ~simpl:false b_case g) s
  in
  [ do_one b Term.mk_true;
    do_one (Term.mk_not ~simpl:false b) Term.mk_false]

(* [ty] must be the type of [m] *)
let message_case (t : Term.message) ty s : sequent list =
  match ty with
  | Type.Boolean -> boolean_case t s
  | _ -> conditional_case t s

(*------------------------------------------------------------------*)
let do_case_tac (args : Args.parser_arg list) s : sequent list =
  match Args.convert_as_lsymb args with
  | Some str when Hyps.mem_name (L.unloc str) s ->
    let id, _ = Hyps.by_name str s in
    List.map (fun (LT.CHyp _, ss) -> ss) (LT.hypothesis_case ~nb:`Any id s)

  | _ ->
    match LT.convert_args s args Args.(Sort ETerm) with
    | Args.Arg (ETerm (ty, f, _)) ->
      begin
        match Type.kind ty with
        | Type.KTimestamp -> LT.timestamp_case f s

        | Type.KMessage -> message_case f ty s

        | Type.KIndex -> bad_args ()
      end
    | _ -> bad_args ()


let case_tac args = LT.wrap_fail (do_case_tac args)

let () =
  T.register_general "case"
    ~tactic_help:
      {general_help = "Perform case analysis on a timestamp, a message built \
                       using a conditional, or a disjunction hypothesis.";
       detailed_help = "A timestamp will be instantiated by all \
                        possible actions, and a message with a conditional will \
                        be split into the two branches.";
       usages_sorts = [Sort Args.Timestamp;
                       Sort Args.String;
                       Sort Args.Message];
       tactic_group = Logical}
    case_tac


(*------------------------------------------------------------------*)
(* TODO: remove, as it is subsumed by the tactic `assumption` ? *)
let false_left s =
  if Hyps.exists (fun _ f -> Term.is_false f) s
  then []
  else Tactics.(soft_failure (Failure "no False assumption"))

let () =
  T.register "false_left"
     ~tactic_help:{general_help = "Closes a goal when False is among its assumptions.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    false_left


(*------------------------------------------------------------------*)
let clear (hid : Ident.t) s = Hyps.remove hid s

let clear_str (hyp_name : lsymb) s =
  let hid,_ = Hyps.by_name hyp_name s in
  clear hid s

let clear_tac_args (args : Args.parser_arg list) s =
  let s =
    List.fold_left (fun s arg -> match arg with
        | Args.String_name arg -> clear_str arg s
        | _ -> bad_args ()
      ) s args in
  [s]

let clear_tac args = LT.wrap_fail (clear_tac_args args)

let () =
  T.register_general "clear"
    ~tactic_help:{
      general_help = "Clear an hypothesis.";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    clear_tac


(*------------------------------------------------------------------*)
(** Apply a And pattern (this is a destruct) of length [l].
    Note that variables in handlers have not been added to the env yet. *)
let do_and_pat (hid : Ident.t) len s : Args.ip_handler list * sequent =
  let destr_fail s =
    soft_failure (Tactics.Failure ("cannot destruct: " ^ s))
  in
  let get_destr ~orig = function
    | Some x -> x
    | None -> destr_fail (Fmt.str "%a" Term.pp orig) in

  assert (len > 0);
  if len = 1 then ([`Hyp hid], s) else
    let form = Hyps.by_id hid s in
    let s = Hyps.remove hid s in

    match form with
    | Term.Atom at ->
      begin
        match Term.destr_matom at with
        | Some (`Eq,a,b) ->
          let a1, a2 = get_destr ~orig:a (destr_pair a)
          and b1, b2 = get_destr ~orig:b (destr_pair b) in

          let f1 = Atom (`Message (`Eq, a1, b1))
          and f2 = Atom (`Message (`Eq, a2, b2)) in

          let forms = List.map (fun x -> Args.Unnamed, x) [f1;f2] in
          let ids, s = Hyps.add_i_list forms s in
          List.map (fun id -> `Hyp id) ids, s

        | _ -> destr_fail (Fmt.str "%a" Term.pp form)
      end

    | Fun (fs,_,_) when fs = Term.f_and ->
      let ands = get_destr ~orig:form (Term.destr_ands len form) in
      let ands = List.map (fun x -> Args.Unnamed, x) ands in
      let ids, s = Hyps.add_i_list ands s in
      List.map (fun id -> `Hyp id) ids, s

    | Term.Exists _ ->
      let vs, f = get_destr ~orig:form (Term.destr_exists form) in

      if List.length vs < len - 1 then
        hard_failure (Tactics.PatNumError (len - 1, List.length vs));

      let vs, vs' = List.takedrop (len - 1) vs in

      let vs_fresh, subst = Term.erefresh_vars `Global vs in

      let f = Term.mk_exists vs' f in
      let f = Term.subst subst f in

      let idf, s = Hyps.add_i Args.Unnamed f s in

      ( (List.map (fun x -> `Var x) vs_fresh) @ [`Hyp idf], s )

    | _ -> destr_fail (Fmt.str "%a" Term.pp form)

(** Apply an And/Or pattern to an ident hypothesis handler. *)
let rec do_and_or_pat (hid : Ident.t) (pat : Args.and_or_pat) s
  : sequent list =
  match pat with
  | Args.And s_ip ->
    (* Destruct the hypothesis *)
    let handlers, s = do_and_pat hid (List.length s_ip) s in

    if List.length handlers <> List.length s_ip then
      hard_failure (Tactics.PatNumError (List.length s_ip, List.length handlers));

    (* Apply, for left to right, the simple patterns, and collect everything *)
    let ss = List.fold_left2 (fun ss handler ip ->
        List.map (do_simpl_pat handler ip) ss
        |> List.flatten
      ) [s] handlers s_ip in
    ss

  | Args.Or s_ip ->
    let ss = LT.hypothesis_case ~nb:(`Some (List.length s_ip)) hid s in

    if List.length ss <> List.length s_ip then
      hard_failure (Tactics.PatNumError (List.length s_ip, List.length ss));

    (* For each case, apply the corresponding simple pattern *)
    List.map2 (fun (LT.CHyp id, s) ip ->
        do_simpl_pat (`Hyp id) ip s
      ) ss s_ip

    (* Collect all cases *)
    |> List.flatten

  | Args.Split ->
    (* Destruct many Or *)
    let ss = LT.hypothesis_case ~nb:`Any hid s in

    (* For each case, apply the corresponding simple pattern *)
    List.map (fun (LT.CHyp id, s) ->
        LT.revert id s
      ) ss

(** Apply an simple pattern a handler. *)
and do_simpl_pat (h : Args.ip_handler) (ip : Args.simpl_pat) s : sequent list =
  match h, ip with
  | _, Args.SNamed n_ip -> [do_naming_pat h n_ip s]

  | `Hyp id, Args.SAndOr ao_ip ->
    do_and_or_pat id ao_ip s

  | `Hyp id, Args.Srewrite dir ->
    let f = Hyps.by_id id s in
    let s = Hyps.remove id s in
    let pat = Term.pat_of_form f in
    let erule = Rewrite.pat_to_rw_erule ~loc:(L.loc dir) (L.unloc dir) pat in
    let s, subgoals = LT.rewrite ~all:false [T_goal] (`Many, Some id, erule) s in
    subgoals @ [s]

  | `Var _, (Args.SAndOr _ | Args.Srewrite _) ->
    hard_failure (Tactics.Failure "intro pattern not applicable")


(*------------------------------------------------------------------*)
(** introduces the topmost variable of the goal. *)
let rec do_intro_var (s : TS.t) : Args.ip_handler * sequent =
  let form = TS.goal s in
  match form with
  | ForAll ((Vars.EVar x) :: vs,f) ->
    let x' = Vars.make_new_from x in

    let subst = [Term.ESubst (Term.Var x, Term.Var x')] in

    let f = match vs with
      | [] -> f
      | _ -> ForAll (vs,f) in

    let new_formula = Term.subst subst f in
    ( `Var (Vars.EVar x'),
      TS.set_goal new_formula s )

  | ForAll ([],f) ->
    (* FIXME: this case should never happen. *)
    do_intro_var (TS.set_goal f s)

  | _ -> soft_failure Tactics.NothingToIntroduce

(** introduces the topmost element of the goal. *)
let rec do_intro (s : TS.t) : Args.ip_handler * sequent =
  let form = TS.goal s in
  match form with
  | ForAll ([],f) ->
    (* FIXME: this case should never happen. *)
    do_intro (TS.set_goal f s)

  | ForAll _ -> do_intro_var s

  | Fun (fs,_,[lhs;rhs]) when fs = Term.f_impl ->
    let id, s = Hyps.add_i Args.Unnamed lhs s in
    let s = TS.set_goal rhs s in
    ( `Hyp id, s )

  | Fun (fs,_,[f]) when fs = Term.f_not ->
    let id, s = Hyps.add_i Args.Unnamed f s in
    let s = TS.set_goal Term.mk_false s in
    ( `Hyp id, s )

  | Atom (`Message (`Neq,u,v)) ->
    let h = `Message (`Eq,u,v) in
    let id, s = Hyps.add_i Args.Unnamed (Atom h) s in
    let s = TS.set_goal Term.mk_false s in
    ( `Hyp id, s )

  | _ -> soft_failure Tactics.NothingToIntroduce

let do_intro_pat (ip : Args.simpl_pat) s : sequent list =
  let handler, s = do_intro s in
  do_simpl_pat handler ip s

(** Correponds to `intro *`, to use in automated tactics. *)
let rec intro_all (s : TS.t) : TS.t list =
  try
    let s_ip = Args.(SNamed AnyName) in
    let ss = do_intro_pat s_ip s in
    List.concat_map intro_all ss

  with Tactics.Tactic_soft_failure (_,NothingToIntroduce) -> [s]

(*------------------------------------------------------------------*)
let do_destruct hid s =
  (* Only destruct the top-most connective *)
  let handlers, s = do_and_pat hid 2 s in
  [List.fold_left (fun s handler ->
       (* TODO: location errors *)
       do_naming_pat handler Args.AnyName s
     ) s handlers]

let destruct_tac_args args s =
  match args with
    | [Args.String_name h; Args.AndOrPat pat] ->
      let hid, _ = Hyps.by_name h s in
      do_and_or_pat hid pat s

    | [Args.String_name h] ->
      let hid, _ = Hyps.by_name h s in
      do_destruct hid s

    | _ -> bad_args ()

let destruct_tac args = LT.wrap_fail (destruct_tac_args args)

let () =
  T.register_general "destruct"
    ~tactic_help:{general_help = "Destruct an hypothesis. An optional And/Or \
                                  introduction pattern can be given.\n\n\
                                  Usages: destruct H.\n\
                                 \        destruct H as [A | [B C]]";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    destruct_tac


(*------------------------------------------------------------------*)
(** Quantifiers *)

(** [goal_exists_intro judge ths] introduces the existentially
    quantified variables in the conclusion of the judgment,
    using [ths] as existential witnesses. *)
let goal_exists_intro  ths (s : TS.t) =
  match TS.goal s with
  | Exists (vs,f) when List.length ths = List.length vs ->
    let table = TS.table s in
    let nu = Theory.parse_subst table (TS.ty_vars s) (TS.env s) vs ths in
    let new_formula = Term.subst nu f in
    [TS.set_goal new_formula s]
  | _ ->
      soft_failure (Tactics.Failure "cannot introduce exists")

(* Does not rely on the typed register, as it parses a subt. *)
let () =
  T.register_general "exists"
    ~tactic_help:{general_help = "Introduce the existentially quantified \
                                  variables in the conclusion of the judgment, \
                                  using the arguments as existential witnesses.\
                                  \n\nUsage: exists v1, v2, ...";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    (fun l s sk fk ->
       let ths =
         List.map
           (function
              | Args.Theory tm -> tm
              | _ -> bad_args ())
           l
       in
         match goal_exists_intro ths s with
           | subgoals -> sk subgoals fk
           | exception Tactics.Tactic_soft_failure e -> fk e)


(*------------------------------------------------------------------*)

let rec simpl_left s =
  let func _ f = match f with
    | Fun (fs, _,_) when fs = Term.f_false || fs = Term.f_and -> true
    | Term.Exists _ -> true
    | _ -> false
  in

  match Hyps.find_opt func s with
  | None -> Some s
  | Some (id,f) ->
    match f with
    | tf when tf = Term.mk_false -> None

    | Exists (vs,f) ->
      let s = Hyps.remove id s in
      let env = ref @@ TS.env s in
      let subst =
        List.map
          (fun (Vars.EVar v) ->
             Term.ESubst  (Term.Var v,
                           Term.Var (Vars.fresh_r env v)))
          vs
      in
      let f = Term.subst subst f in
      simpl_left (Hyps.add Args.AnyName f (TS.set_env !env s))

    | _ as form ->
      let f, g = oget (Term.destr_and form) in
      let s = Hyps.remove id s in
      simpl_left (Hyps.add_list [(Args.AnyName, f); (Args.AnyName, g)] s)

let simpl_left_tac s = match simpl_left s with
  | None -> []
  | Some s -> [s]

let () =
  T.register "simpl_left"
    ~tactic_help:{general_help = "Introduce all conjunctions, existentials and \
                                  false hypotheses.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    simpl_left_tac

(*------------------------------------------------------------------*)
let () =
  T.register_general "generalize"
    ~tactic_help:{
      general_help = "Generalize the goal on some terms";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    (LT.generalize_tac ~dependent:false)

let () =
  T.register_general "generalize dependent"
    ~tactic_help:{
      general_help = "Generalize the goal and hypotheses on some terms";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    (LT.generalize_tac ~dependent:true)

(*------------------------------------------------------------------*)
(** Induction *)

let induction s  =
  let error () =
    Tactics.soft_failure
      (Tactics.Failure
         "conclusion must be an universal quantification over a timestamp")
  in

  match TS.goal s with
  | ForAll ((Vars.EVar v)::vs,f) ->
    begin
      match Vars.ty v with
        Type.Timestamp ->
        (
          (* We need two fresh variables in env,
           * but one will not be kept in the final environment. *)
          let env,v' = Vars.fresh (TS.env s) v in
          let _,v'' = Vars.fresh env v in
          (* Introduce v as v'. *)
          let f' = match vs with
            | [] -> f
            | _ -> ForAll (vs,f) in
          let f' = Term.subst [Term.ESubst (Term.Var v,Term.Var v')] f' in
          (* Use v'' to form induction hypothesis. *)
          let (-->) a b = mk_impl a b in
          let ih =
            ForAll ((Vars.EVar v'') :: vs,
                    (Atom (`Timestamp (`Lt,Term.Var v'',Term.Var v)
                           :> generic_atom) -->
                     Term.subst
                       [Term.ESubst (Term.Var v,Term.Var v'')] f)) in

          let goal = Term.mk_impl ih f' in

          let s = TS.set_env env s
                  |> TS.set_goal goal in
          [s]
        )
      | _ -> error ()
    end

  | _ -> error ()

let () = T.register "induction"
    ~tactic_help:{general_help = "Apply the induction scheme to the conclusion.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    induction

(*------------------------------------------------------------------*)
(** [assumption judge sk fk] proves the sequent using the axiom rule. *)
let assumption (s : TS.t) =
  let goal = TS.goal s in
  if goal = Term.mk_true ||
     Hyps.is_hyp goal s ||
     Hyps.is_hyp Term.mk_false s then
    let () = dbg "assumption %a" Term.pp goal in
    []

  else soft_failure Tactics.NotHypothesis

let () = T.register "assumption"
    ~tactic_help:{
      general_help = "Search for the conclusion inside the hypothesis.";
      detailed_help = "";
      usages_sorts = [Sort None];
      tactic_group = Logical }
    assumption


(*------------------------------------------------------------------*)
(** [use ip name ths judge] applies the formula named [gp],
  * eliminating its universally quantified variables using [ths],
  * and eliminating implications (and negations) underneath.
  * If given an introduction patterns, apply it to the generated hypothesis. *)
let use ip (name : lsymb) (ths : Theory.term list) (s : TS.t) =
  (* Get formula to apply. *)
  let lem = TS.get_reach_hyp_or_lemma name s in

  (* FIXME *)
  if lem.gc_tyvars <> [] then
    Tactics.(soft_failure (Failure "free type variables not supported with \
                                    use tactic")) ;

  (* Get universally quantified variables, verify that lengths match. *)
  let uvars,f = match lem.gc_concl with
    | ForAll (uvars,f) -> uvars,f
    | _ as f           -> [],f in

  if List.length uvars < List.length ths then
    Tactics.(soft_failure (Failure "too many arguments")) ;
  
  let uvars, uvars0 = List.takedrop (List.length ths) uvars in
  let f = Term.mk_forall ~simpl:false uvars0 f in

  (* refresh *)
  let uvars, subst = Term.erefresh_vars `Global uvars in
  let f = Term.subst subst f in

  let subst = 
    Theory.parse_subst (TS.table s) (TS.ty_vars s) (TS.env s) uvars ths 
  in

  (* instantiate [f] *)
  let f = Term.subst subst f in

  (* Compute subgoals by introducing implications on the left. *)
  let rec aux subgoals = function
    | Fun (fs,_,[h;c]) when fs = Term.f_impl ->
        let s' = TS.set_goal h s in
        aux (s'::subgoals) c

    | Fun (fs,_,[h]) when fs = Term.f_not ->
        let s' = TS.set_goal h s in
        List.rev (s'::subgoals)

    | f ->
      let idf, s0 = Hyps.add_i Args.AnyName f s in
      let s0 = match ip with
        | None -> [s0]
        | Some ip -> do_simpl_pat (`Hyp idf) ip s0 in
      s0 @ List.rev subgoals
  in

  aux [] f

(* this is the `use` tactic. *)
let tac_apply args s sk fk =
  let ip, args = match args with
    | Args.SimplPat ip :: args -> Some ip, args
    | args                     -> None, args in
  match args with
  | Args.String_name id :: th_terms ->
    let th_terms =
      List.map
        (function
          | Args.Theory th -> th
          | _ -> bad_args ())
        th_terms
    in
    begin match use ip id th_terms s with
      | subgoals -> sk subgoals fk
      | exception Tactics.Tactic_soft_failure e -> fk e
    end
  | _ -> bad_args ()


let tac_apply args s sk fk =
  try tac_apply args s sk fk with
  | Tactics.Tactic_soft_failure e-> fk e

(* Does not rely on the typed register as it parses a subst *)
let () =
  T.register_general "use"
    ~tactic_help:{general_help = "Apply an hypothesis with its universally \
                                  quantified variables instantiated with the \
                                  arguments.\n\n\
                                  Usages: use H with v1, v2, ...\n\
                                 \        use H with ... as ...";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    tac_apply

(*------------------------------------------------------------------*)
(** [tac_assert f j sk fk] generates two subgoals, one where [f] needs
  * to be proved, and the other where [f] is assumed. *)
let tac_assert (args : Args.parser_arg list) s sk fk =
  try
    let ip, f = match args with
      | [f] -> None, f
      | [f; Args.SimplPat ip] -> Some ip, f
      | _ -> bad_args () in

    let f = match LT.convert_args s [f] Args.(Sort Boolean) with
      | Args.(Arg (Boolean f)) -> f
      | _ -> bad_args () in

    let s1 = TS.set_goal f s in
    let id, s2 = Hyps.add_i Args.AnyName f s in
    let s2 = match ip with
      | Some ip -> do_simpl_pat (`Hyp id) ip s2
      | None -> [s2] in
    sk (s1 :: s2) fk

  with Tactics.Tactic_soft_failure e -> fk e

let () =
  T.register_general "assert"
    ~tactic_help:{general_help = "Add an assumption to the set of hypothesis, \
                                  and produce the goal for\
                                  \nthe proof of the assumption.\n\
                                  Usages: assert f.\n \
                                 \       assert f as intro_pat";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    tac_assert


(*------------------------------------------------------------------*)
(** {2 Structural Tactics} *)

let happens_premise (s : sequent) (a : Term.timestamp) =
  TS.set_goal (Term.Atom (`Happens a)) s

(*------------------------------------------------------------------*)
let depends Args.(Pair (Timestamp a1, Timestamp a2)) s =
  match a1, a2 with
  | Term.Action(n1, is1), Term.Action (n2, is2) ->
    let table = TS.table s in
    if Action.(depends (of_term n1 is1 table) (of_term n2 is2 table)) then
        let atom = (Atom (`Timestamp (`Lt,a1,a2))) in
        let g = Term.mk_impl ~simpl:false atom (TS.goal s) in
        [happens_premise s a2;
         TS.set_goal g s]
    else
      soft_failure
        (Tactics.NotDepends (Fmt.strf "%a" Term.pp a1,
                             Fmt.strf "%a" Term.pp a2))
  | _ -> soft_failure (Tactics.Failure "arguments must be actions")

let () =
  T.register_typed "depends"
    ~general_help:"If the second action depends on the first \
                   action, and if the second \
                   action happened, \
                   add the corresponding timestamp inequality."
    ~detailed_help:"Whenever action A1[i] must happen before A2[i], if A2[i] \
                    occurs in the trace, we can add A1[i]. "
    ~tactic_group:Structural
    depends Args.(Pair (Timestamp, Timestamp))



(*------------------------------------------------------------------*)
(** [congruence judge sk fk] try to close the goal using congruence, else
    calls [fk] *)
let congruence (s : TS.t) : bool =
  match simpl_left s with
  | None -> true
  | Some s ->
    let conclusions =
      Utils.odflt [] (Term.disjunction_to_literals (TS.goal s))
    in

    let term_conclusions =
      List.fold_left (fun acc conc -> match conc with
          | `Pos, (#generic_atom as at) ->
            let at = (at :> Term.generic_atom) in
            Term.(mk_not (Atom at)) :: acc
          | `Neg, (#generic_atom as at) ->
            Term.Atom at :: acc)
        []
        conclusions
    in
    let s = List.fold_left (fun s f ->
        Hyps.add Args.AnyName f s
      ) s term_conclusions
    in
    TS.eq_atoms_valid s

(** [constraints s] proves the sequent using its trace formulas. *)
let congruence_tac (s : TS.t) =
  match congruence s with
  | true ->
    let () = dbg "closed by congruence" in
    []

  | false ->
    let () = dbg "congruence failed" in
    soft_failure Tactics.CongrFail

let () = T.register "congruence"
    ~tactic_help:
      {general_help = "Tries to derive false from the messages equalities.";
       detailed_help = "It relies on the reflexivity, transitivity \
                        and stability by function application \
                        (f(u)=f(v) <=> u=v).";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    congruence_tac

(*------------------------------------------------------------------*)
let constraints (s : TS.t) =
  match simpl_left s with
  | None -> true
  | Some s ->
    let conclusions =
      Utils.odflt [] (Term.disjunction_to_literals (TS.goal s))
    in
    let trace_conclusions =
      List.fold_left (fun acc conc -> match conc with
          | `Pos, (#trace_atom as at) ->
            let at = (at :> Term.generic_atom) in
            Term.(mk_not (Atom at)) :: acc
          | `Neg, (#trace_atom as at) ->
            Term.Atom at :: acc
          | _ -> acc)
        []
        conclusions
    in
    let s = List.fold_left (fun s f ->
        Hyps.add Args.AnyName f s
      ) s trace_conclusions
    in
    TS.constraints_valid s

(** [constraints s] proves the sequent using its trace formulas. *)
let constraints_tac (s : TS.t) =
  match constraints s with
  | true ->
    let () = dbg "closed by constraints" in
    []

  | false ->
   let () = dbg "constraints failed" in
   soft_failure (Tactics.Failure "constraints satisfiable")

let () = T.register "constraints"
    ~tactic_help:
      {general_help = "Tries to derive false from the trace formulas.";
       detailed_help = "From ordering constraints on the timestamps, \
                        checks that we can build an acyclic graph on \
                        them, i.e., if they are a possible trace.";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    constraints_tac



(*------------------------------------------------------------------*)
(** Length *)

let namelength Args.(Pair (Message (tn, tyn), Message (tm, tym))) s =
  match tn, tm with
  | Name n, Name m ->
    let table = TS.table s in

    (* TODO: subtypes *)
    if not (tyn = tym) then
      Tactics.soft_failure (Failure "names are not of the same types");

    if not Symbols.(check_bty_info table n.s_typ Ty_name_fixed_length) then
      Tactics.soft_failure
        (Failure "names are of a type that is not [name_fixed_length]");

    let f = Term.(Atom (`Message (`Eq,
                                  Term.mk_len (Name n),
                                  Term.mk_len (Name m)))) in

    [TS.set_goal
       (Term.mk_impl ~simpl:false f (TS.goal s)) s]

  | _ -> Tactics.(soft_failure (Failure "expected names"))

let () =
  T.register_typed "namelength"
    ~general_help:"Adds the fact that two names have the same length."
    ~detailed_help:""
    ~tactic_group:Structural
    namelength Args.(Pair (Message, Message))

(*------------------------------------------------------------------*)
(** Eq-Indep Axioms *)

(* We include here rules that are specialization of the Eq-Indep axiom. *)

(** Add index constraints resulting from names equalities, modulo the TRS.
    The judgment must have been completed before calling [eq_names]. *)
let eq_names (s : TS.t) =
  let trs   = TS.get_trs s in
  let table = TS.table s in
  let terms = TS.get_all_messages s in
  (* we start by collecting equalities between names implied by the indep axiom.
  *)
  let new_eqs =
    Completion.name_indep_cnstrs table trs terms
  in
  let s =
    List.fold_left (fun s c ->
        let () = dbg "new name equality (indep): %a" Term.pp c in
        Hyps.add Args.AnyName c s
      ) s new_eqs in

  (* we now collect equalities between timestamp implied by equalities between
     names. *)
  let trs = TS.get_trs s in
  let cnstrs =
    Completion.name_index_cnstrs table trs (TS.get_all_messages s)
  in
  let s =
    List.fold_left (fun s c ->
        let () = dbg "new index equality (names): %a" Term.pp c in
        Hyps.add Args.AnyName c s
      ) s cnstrs
  in
  [s]

let () = T.register "eqnames"
    ~tactic_help:
      {general_help = "Add index constraints resulting from names equalities, \
                       modulo the known equalities.";
       detailed_help = "If n[i] = n[j] then i = j. \
                        This is checked on all name equality entailed \
                        by the current context.";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    eq_names

(*------------------------------------------------------------------*)
(** Add terms constraints resulting from timestamp and index equalities. *)
let eq_trace (s : TS.t) =
  let ts_classes = TS.get_ts_equalities ~precise:false s
  in
  let ts_classes = List.map (List.sort_uniq Stdlib.compare) ts_classes in
  let ts_subst =
    let rec asubst e = function
        [] -> []
      | p::q -> Term.ESubst (p,e) :: (asubst e q)
    in
    List.map (function [] -> [] | p::q -> asubst p q) ts_classes
    |> List.flatten
  in
  let ind_classes = TS.get_ind_equalities ~precise:false s
  in
  let ind_classes = List.map (List.sort_uniq Stdlib.compare) ind_classes in
  let ind_subst =
    let rec asubst e = function
        [] -> []
      | p::q -> Term.ESubst (Term.Var p,Term.Var e) :: (asubst e q)
    in
    (List.map (function [] -> [] | p::q -> asubst p q) ind_classes)
    |> List.flatten
  in
  let terms = TS.get_all_messages s in
  let facts =
    List.fold_left
      (fun acc t ->
         let normt : Term.message = Term.subst (ts_subst @ ind_subst) t in
         if normt = t then
           acc
         else
           Term.Atom (`Message (`Eq, t, normt)) ::acc)
      [] terms
  in
  let s =
    List.fold_left (fun s c ->
        let () = dbg "new trace equality: %a" Term.pp c in
        Hyps.add Args.AnyName c s
      ) s facts
  in
  [s]

let () = T.register "eqtrace"
    ~tactic_help:
      {general_help = "Add terms constraints resulting from timestamp \
                       and index equalities.";
       detailed_help = "Whenver i=j or ts=ts', we can substitute one \
                        by another in the other terms.";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    eq_trace

(*------------------------------------------------------------------*)
let fresh_param m1 m2 = match m1,m2 with
  | Name ns, _ -> (ns, m2)
  | _, Name ns -> (ns, m1)
  | _ ->
    soft_failure
      (Tactics.Failure "can only be applied on hypothesis of the form \
                        t=n or n=t")

(* Direct cases - names appearing in the term [t] *)
let mk_fresh_direct (cntxt : Constr.trace_cntxt) env ns t =
  (* iterate over [t] to search subterms of [t] equal to a name *)
  let list_of_indices =
    let iter = new Fresh.get_name_indices ~cntxt false ns.s_symb in
    iter#visit_message t ;
    iter#get_indices
  in

  (* build the formula expressing that there exists a name subterm of [t]
   * equal to the name ([n],[is]) *)
  let mk_case (js : Type.index Vars.var list) =
    (* select bound variables *)
    let bv = List.filter (fun i -> not (Vars.mem env i)) js in

    let env_local = ref env in
    let bv' = List.map (Vars.fresh_r env_local) bv in

    let subst =
      List.map2
        (fun i i' -> ESubst (Term.Var i, Term.Var i'))
        bv bv'
    in

    let js = List.map (Term.subst_var subst) js in

    Term.mk_exists
      (List.map (fun i -> Vars.EVar i) bv')
      (Term.mk_indices_eq ns.s_indices js)
  in

  let cases = List.map mk_case list_of_indices in
  Term.mk_ors (List.sort_uniq Stdlib.compare cases)

(* Indirect cases - names ([n],[is']) appearing in actions of the system *)
let mk_fresh_indirect (cntxt : Constr.trace_cntxt) env ns t : Term.message =
  let list_of_actions_from_term =
    let iter = new Fresh.get_actions ~cntxt in
    iter#visit_message t ;
    iter#get_actions in

  let tbl_of_action_indices = ref [] in

  let () = SystemExpr.(iter_descrs cntxt.table cntxt.system
    (fun action_descr ->
      let iter = new Fresh.get_name_indices ~cntxt true ns.s_symb in
      iter#visit_message (snd action_descr.condition) ;
      iter#visit_message (snd action_descr.output) ;
      List.iter (fun (_,t) -> iter#visit_message t) action_descr.updates;
      (* we add only actions in which name [n] occurs *)
      let action_indices = iter#get_indices in
      if List.length action_indices > 0 then
        tbl_of_action_indices :=
          (action_descr, action_indices)
          :: !tbl_of_action_indices))
  in

  (* the one case occuring in [a] with indices [is_a].'
     For n[is] to be equal to n[is_a], we must have is=is_a.
     Hence we substitute is_a by is. *)
  let mk_case a is_a =
    let env_local = ref env in

    (* We only quantify over indices that are not in is_a *)
    let eindices =
      List.filter (fun v -> not (List.mem v is_a)) a.Action.indices in

    let eindices' =
      List.map (Vars.fresh_r env_local) eindices in

    (* refresh existantially quant. indices, and subst is_a by is. *)
    let subst =
      List.map2
        (fun i i' -> ESubst (Term.Var i, Term.Var i'))
        (eindices @ is_a) (eindices' @ ns.s_indices)
    in

    (* we apply [subst] to the action [a] *)
    let new_action =
      SystemExpr.action_to_term cntxt.table cntxt.system
        (Action.subst_action subst a.Action.action) in

    let timestamp_inequalities =
      Term.mk_ors
        (List.map (fun action_from_term ->
             Term.Atom (Term.mk_timestamp_leq
                          new_action
                          action_from_term)
           ) list_of_actions_from_term)
    in

    (* Remark that the equations below are not redundant.
       Indeed, assume is = (i,j) and is_a = (i',i').
       Then, the substitution [subst] will map i' to i
       (the second substitution i->j is shadowed)
       But, by substituting in the vector of equalities, we correctly retrieve
       that i = j. *)
    let idx_eqs =
      Term.mk_indices_eq ns.s_indices (List.map (Term.subst_var subst) is_a)
    in

    Term.mk_exists
      (List.map (fun i -> Vars.EVar i) eindices')
      (Term.mk_and
         timestamp_inequalities
         idx_eqs)
  in

  (* Do all cases of action [a] *)
  let mk_cases_descr (a, indices_a) =
    List.map (mk_case a) indices_a in

  let cases = List.map mk_cases_descr !tbl_of_action_indices
              |> List.flatten in

  mk_ors cases


let fresh (Args.String m) s =
  try
    let id,hyp = Hyps.by_name m s in
    let hyp = LT.expand_all_term hyp s in
    let table = TS.table s in
    let env   = TS.env s in

    begin match hyp with
      | Atom (`Message (`Eq,m1,m2)) ->
        let (ns,t) = fresh_param m1 m2 in

        let ty = ns.s_typ in
        if not Symbols.(check_bty_info table ty Ty_large) then
          Tactics.soft_failure
            (Failure "the type of this term is not [large]");

        let cntxt = TS.mk_trace_cntxt s in
        let phi_direct = mk_fresh_direct cntxt env ns t in
        let phi_indirect = mk_fresh_indirect cntxt env ns t in

        let phi = Term.mk_or phi_direct phi_indirect in

        let goal = Term.mk_impl ~simpl:false phi (TS.goal s) in
        [TS.set_goal goal s]

      | _ -> soft_failure
               (Tactics.Failure "can only be applied on message hypothesis")
    end
  with
  | Fresh.Var_found ->
    soft_failure
      (Tactics.Failure "can only be applied on ground terms")

let () =
  T.register_typed "fresh"
    ~general_help:"Given a message equality M of the form t=n, \
                   add an hypothesis expressing that n is a subterm of t."
    ~detailed_help:"This condition checks that all occurences of the same name \
                    in other actions cannot have happened before this action."
    ~tactic_group:Structural
    fresh Args.String

(*------------------------------------------------------------------*)
let apply_substitute subst s =
    let s =
    match subst with
      | Term.ESubst (Term.Var v, t) :: _ when
        not (List.mem (Vars.EVar v) (Term.get_vars t)) ->
          TS.set_env (Vars.rm_var (TS.env s) v) s
      | _ -> s
  in
  [TS.subst subst s]

let substitute_mess (m1, m2) s =
  let subst =
        let trs = TS.get_trs s in
        if Completion.check_equalities trs [Term.ESubst (m1,m2)] then
          [Term.ESubst (m1,m2)]
        else
          soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_ts (ts1, ts2) s =
  let subst =
      let models = TS.get_models s in
      if Constr.query ~precise:true models [(`Pos, `Timestamp (`Eq,ts1,ts2))] then
        [Term.ESubst (ts1,ts2)]
      else
        soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_idx (i1 , i2 : Type.index Term.term * Type.index Term.term) s =
  let i1, i2 =  match i1, i2 with
    | Var i1, Var i2 -> i1, i2
    | (Diff _), _ | _, (Diff _) ->
      hard_failure
        (Tactics.Failure "only variables are supported when substituting \
                          index terms")
  in

  let subst =
    let models = TS.get_models s in
    if Constr.query ~precise:true models [(`Pos, `Index (`Eq,i1,i2))] then
      [Term.ESubst (Term.Var i1,Term.Var i2)]
    else
      soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_tac arg s =
  let open Args in
  match arg with
  | Pair (ETerm (Type.Message, f1, _), ETerm (Type.Message, f2, _)) ->
    substitute_mess (f1,f2) s

  | Pair (ETerm (Type.Timestamp, f1, _), ETerm (Type.Timestamp, f2, _)) ->
    substitute_ts (f1,f2) s

  | Pair (ETerm (Type.Index, f1, _), ETerm (Type.Index, f2, _)) ->
    substitute_idx (f1,f2) s

  | _ ->
    hard_failure
      (Tactics.Failure "expected a pair of messages, booleans or a pair of \
                        index variables")

let () =
  T.register_typed "subst"
    ~general_help:"If i = t where i is a variable, substitute all occurences \
                   of i by t and remove i from the context variables."
    ~detailed_help:""
    ~tactic_group:Structural
    ~usages_sorts:[Args.(Sort (Pair (Index, Index)));
                   Args.(Sort (Pair (Timestamp, Timestamp)));
                   Args.(Sort (Pair (Message, Message)))]
    substitute_tac Args.(Pair (ETerm, ETerm))



(*------------------------------------------------------------------*)
let autosubst s =
  let id, f = match
      Hyps.find_map
        (fun id f -> match f with
           | Atom (`Timestamp (`Eq, Term.Var x, Term.Var y) as atom) ->
             Some (id, atom)
           | Atom (`Index (`Eq, x, y) as atom) ->
             Some (id,atom)
           | _ -> None)
        s
    with | Some (id,f) -> id, f
         | None -> Tactics.(soft_failure (Failure "no equality found"))
  in
  let s = Hyps.remove id s in

  let process : type a. a Vars.var -> a Vars.var -> TS.t =
    fun x y ->

      (* Just remove the equality if x and y are the same variable. *)
      if x = y then s else
      (* Otherwise substitute the newest variable by the oldest one,
       * and remove it from the environment. *)
      let x,y =
        if Vars.compare x y <= 0 then y,x else x,y
      in

      let () = dbg "subst %a by %a" Vars.pp x Vars.pp y in

      let s =
        TS.set_env (Vars.rm_var (TS.env s) x) s
      in
        TS.subst [Term.ESubst (Term.Var x, Term.Var y)] s
  in
    match f with
    | `Timestamp (`Eq, Term.Var x, Term.Var y) -> [process x y]
    | `Index (`Eq, x, y)                       -> [process x y]
    | _ -> assert false

(*------------------------------------------------------------------*)
(* TODO: this should be an axiom in some library, not a rule *)
let exec (Args.Timestamp a) s =
  let _,var = Vars.make `Approx (TS.env s) Type.Timestamp "t" in
  let formula =
    Term.ForAll
      ([Vars.EVar var],
       Term.mk_impl
         (Atom (Term.mk_timestamp_leq (Var var) a))
         (Macro(Term.exec_macro,[],Var var)))
  in
  [happens_premise s a ;

   TS.set_goal Term.(Macro (exec_macro,[],a)) s;

    TS.set_goal
      (Term.mk_impl ~simpl:false formula (TS.goal s)) s]

let () =
  T.register_typed "executable"
    ~general_help:"Assert that exec@_ implies exec@_ for all \
                   previous timestamps."
    ~detailed_help:"This is by definition of exec, which is the conjunction of \
                    all conditions before this timestamp."
    ~tactic_group:Structural
    exec Args.Timestamp


(*------------------------------------------------------------------*)
(** [fa s] handles some goals whose conclusion formula is of the form
  * [C(u_1..u_N) = C(v_1..v_N)] and reduced them to the subgoals with
  * conclusions [u_i=v_i]. We only implement it for the constructions
  * [C] that congruence closure does not support: conditionals,
  * sequences, etc. *)
let fa s =
  let unsupported () =
    Tactics.(soft_failure (Failure "equality expected")) in

  match TS.goal s with
    | Term.Atom (`Message (`Eq,u,v)) ->
        begin match u,v with

          | Term.Fun (f,_,[c;t;e]), Term.Fun (f',_,[c';t';e'])
            when f = Term.f_ite && f' = Term.f_ite ->
            let subgoals =
              let open TraceSequent in
              [ s |> set_goal (Term.mk_impl c c') ;

                s |> set_goal (Term.mk_impl c' c) ;

                s |> set_goal (Term.mk_impls
                                       (if c = c' then [c] else [c;c'])
                                       (Term.Atom (`Message (`Eq,t,t'))));

                s |> set_goal (Term.mk_impls
                                       [Term.mk_not c;
                                        Term.mk_not c']
                                       (Term.Atom (`Message (`Eq,e,e')))) ]
            in
            subgoals

          | Term.Seq (vars,t),
            Term.Seq (vars',t') when vars = vars' ->
            let env = ref (TS.env s) in
            let vars' = List.map (Vars.fresh_r env) vars in
            let s = TS.set_env !env s in
            let subst =
              List.map2
                (fun i i' -> ESubst (Term.Var i, Term.Var i'))
                vars vars'
            in
            let t = Term.subst subst t in
            let t' = Term.subst subst t' in
            let subgoals =
              [ TS.set_goal
                  (Term.Atom (`Message (`Eq,t,t'))) s ]
            in
            subgoals

          | Term.Find (vars,c,t,e),
            Term.Find (vars',c',t',e') when vars = vars' ->
            (* We could simply verify that [e = e'],
             * and that [t = t'] and [c <=> c'] for fresh index variables.
             *
             * We do something more general for the conditions,
             * which is useful for cases arising from diff-equivalence
             * where some indices are unused on one side:
             *
             * Assume [vars = used@unused]
             * where [unusued] variables are unused in [c] and [t].
             *
             * We verify that [forall used. (c <=> exists unused. c')]:
             * this ensures that if one find succeeds, the other does
             * too, and also that the selected indices will match
             * except for the [unused] indices on the left, which does
             * not matter since they do not appear in [t]. *)

            (* Refresh bound variables. *)
            let env = ref (TS.env s) in
            let vars' = List.map (Vars.fresh_r env) vars in
            let s = TS.set_env !env s in
            let subst =
              List.map2
                (fun i i' -> ESubst (Term.Var i, Term.Var i'))
                vars vars'
            in
            let c  = Term.subst subst c in
            let c' = Term.subst subst c' in
            let t  = Term.subst subst t in
            let t' = Term.subst subst t' in

            (* Extract unused variables. *)
            let used,unused =
              let occ_vars = Term.get_vars c @ Term.get_vars t in
              let vars = List.map (fun i -> Vars.EVar i) vars' in
              List.partition
                (fun v -> List.mem v occ_vars)
                vars
            in

            let subgoals =
              let open TraceSequent in
              [ set_goal
                  (Term.mk_impl c (Term.mk_exists unused c')) s ;

                set_goal (Term.mk_impl c' c) s;

                set_goal (Term.mk_impls [c;c']
                                  (Atom (`Message (`Eq,t,t')))) s;

                set_goal (Term.Atom (`Message (`Eq,e,e'))) s]
            in
            subgoals

          | _ -> Tactics.(soft_failure (Failure "unsupported equality"))
        end
    | _ -> unsupported ()

let () =
  T.register "fa"
    ~tactic_help:{general_help = "Break down some conclusion equalities into the \
                                  equalities of their subterms.";
                  detailed_help = "When we have G => f(u) = f(v), produces the \
                                   goal G => u=v. Produces as many subgoals as \
                                   arugment of the head function symbol. Recall \
                                   that everything is a function, notably, if \
                                   then else and try find construct are.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    fa

(*------------------------------------------------------------------*)
let remember (id : Theory.lsymb) (term : Theory.term) s =
  match LT.econvert s term with
  | None -> soft_failure ~loc:(L.loc term) (Failure "type error")
  | Some (Theory.ETerm (ty, t, _)) ->
    let env, x = LT.make_exact ~loc:(L.loc id) (TS.env s) ty (L.unloc id) in
    let subst = [Term.ESubst (t, Term.Var x)] in

    let s = TS.subst subst (TS.set_env env s) in
    let eq = Term.mk_atom `Eq (Term.Var x) t in
    TS.set_goal (Term.mk_impl ~simpl:false eq (TS.goal s)) s

let remember_tac_args (args : Args.parser_arg list) s : sequent list =
  match args with
  | [Args.Remember (term, id)] -> [remember id term s]
  | _ -> bad_args ()

let remember_tac args = LT.wrap_fail (remember_tac_args args)

let () =
  T.register_general "remember"
    ~tactic_help:{
      general_help = "substitute a term by a fresh variable";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    remember_tac

(*------------------------------------------------------------------*)
(** New goal simplification *)


let new_simpl ~congr ~constr s =
  let s = LT.reduce_sequent s in
  let goals = Term.decompose_ands (TS.goal s) in
  let goals = List.filter_map (fun goal ->
      if Hyps.is_hyp goal s || Term.f_triv goal then None
      else match goal with
        | Term.Atom Term.(#trace_atom as at) ->
          if constr && Constr.query ~precise:true (TS.get_models s) [`Pos, at]
          then None
          else Some goal

        | Term.Atom (`Message (`Eq, t1, t2)) ->
          if congr &&
             Completion.check_equalities (TS.get_trs s) [Term.ESubst (t1,t2)]
          then None
          else Some goal

        | _ -> Some goal
    ) goals in
  [TS.set_goal (Term.mk_ands goals) s]


(*------------------------------------------------------------------*)
(** Automated goal simplification *)

let clear_triv s sk fk = sk [Hyps.clear_triv s] fk

(** Simplify goal. *)
let _simpl ~close ~strong =
  let open Tactics in
  let intro = Config.auto_intro () in

  let assumption = if close then [try_tac (LT.wrap_fail assumption)] else [] in

  let new_simpl ~congr ~constr =
    if strong && not intro
    then [LT.wrap_fail (new_simpl ~congr ~constr)] @ assumption
    else []
  in

  let expand_all =
    (if strong && close && not intro
     then [LT.wrap_fail (LT.expand_all_l `All)] @ assumption
     else [])
  in


  andthen_list ~cut:true (
    (* Try assumption first to avoid loosing the possibility
       * of doing it after introductions. *)
    assumption @
    (new_simpl ~congr:false ~constr:false) @
    (if close || intro then [LT.wrap_fail intro_all;
                             LT.wrap_fail simpl_left_tac] else []) @
    assumption @
    expand_all @
    (* Learn new term equalities from constraints before
     * learning new index equalities from term equalities,
     * otherwise this creates e.g. n(j)=n(i) from n(i)=n(j). *)
    (* (if intro then [wrap eq_trace] else []) @ *)
    (if strong then [LT.wrap_fail eq_names] else []) @
    (* Simplify equalities using substitution. *)
    (repeat ~cut:true (LT.wrap_fail autosubst)) ::
    expand_all @
    assumption @ (new_simpl ~congr:true ~constr:true) @
    [clear_triv]
  )

(*------------------------------------------------------------------*)
(* Attempt to close a goal. *)
let do_conclude =
  Tactics.orelse_list [LT.wrap_fail congruence_tac;
                       LT.wrap_fail constraints_tac;
                       LT.wrap_fail assumption]



(* If [close] then tries to automatically prove the goal,
 * otherwise it may also be reduced to a single subgoal. *)
let rec simpl ~strong ~close : TS.t Tactics.tac =
  let open Tactics in
  let (>>) = andthen ~cut:true in
  (* if [close], we introduce as much as possible to help. *)
  _simpl ~close ~strong >>

  if not strong
  then (fun g sk fk -> sk [g] fk)
  else
    (if close || Config.auto_intro ()
     then try_tac do_conclude else Tactics.id) >>
    fun g sk fk ->
    (* If we still have a goal, we can try to split a conjunction
     * and prove the remaining subgoals, or return this goal,
     * but we must respect [close]. *)
    let fk =
      if close
      then fun _ -> fk (None, GoalNotClosed)
      else fun _ -> sk [g] fk
    in
    (LT.wrap_fail goal_and_right) g
      (fun l _ -> match l with
         | [g1;g2] ->
           simpl ~strong ~close g1
             (fun l' _ ->
                if l'=[] then
                  simpl ~strong ~close g2 sk fk
                else
                  simpl ~strong ~close:true g2
                    (fun l'' fk -> assert (l'' = []) ; sk l' fk)
                    fk)
             fk
         | _ -> assert false)
      fk

let () = T.register_general "autosimpl"
    ~tactic_help:{general_help = "Simplify a goal, without closing \
                                  it. Automatically called after each tactic.";
                  detailed_help = "Performs introductions, eqtrace and eqnames.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    (function
      | [] -> simpl ~strong:(Config.auto_intro ()) ~close:false
      | _ -> hard_failure (Tactics.Failure "no argument allowed")) ;

  T.register_general "simpl"
    ~tactic_help:{general_help = "Simplifies a goal.";
                  detailed_help = "Performs introductions, eqtrace and eqnames.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    (function
      | [] -> simpl ~strong:true ~close:false
      | _ -> hard_failure (Tactics.Failure "no argument allowed")) ;

  T.register_general "auto"
     ~tactic_help:{general_help = "Closes a goal.";
                   detailed_help = "Behaves like simpl, but also calls \
                                    congruence, constraints and assumption.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    (function
       | [] -> simpl ~strong:true ~close:true
       | _ -> hard_failure (Tactics.Failure "no argument allowed"))


(*------------------------------------------------------------------*)
let do_s_item (s_item : Args.s_item) s : TS.sequent list =
  match s_item with
  | Args.Simplify l ->
    let tac = simpl ~strong:true ~close:false in
    Tactics.run tac s

  | Args.Tryauto l ->
    let tac = Tactics.try_tac (simpl ~strong:true ~close:true) in
    Tactics.run tac s

(** Applies a rewrite arg  *)
let do_rw_arg rw_arg rw_in s : TS.sequent list =
  match rw_arg with
  | Args.R_item rw_item  -> LT.do_rw_item rw_item rw_in s
  | Args.R_s_item s_item -> do_s_item s_item s (* targets are ignored there *)

let rewrite_tac args s =
  match args with
  | [Args.RewriteIn (rw_args, in_opt)] ->
    List.fold_left (fun seqs rw_arg ->
        List.concat_map (do_rw_arg rw_arg in_opt) seqs
      ) [s] rw_args

  | _ -> bad_args ()

let rewrite_tac args = LT.wrap_fail (rewrite_tac args)

let () =
  T.register_general "rewrite"
    ~tactic_help:{
      general_help =
        "If t1 = t2, rewrite all occurences of t1 into t2 in the goal.\n\
         Usage: rewrite Hyp Lemma Axiom (forall (x:message), t = t').\n       \
         rewrite Lemma Axiom (t=t').\n       \
         rewrite (forall (x:message), t = t').\n       \
         rewrite (t = t') Lemma in H.";
      detailed_help = "";
      usages_sorts  = [];
      tactic_group  = Structural;}
    rewrite_tac


(*------------------------------------------------------------------*)
let apply (pat : Term.message Term.pat) (s : TS.t) : TS.t list =
  let subs, f = Term.decompose_impls_last pat.pat_term in

  if not (Vars.Sv.subset pat.pat_vars (Term.fv f)) then
    soft_failure ApplyBadInst;

  let pat = { pat with pat_term = f } in

  match Term.Match.try_match (TS.goal s) pat with
  | `NoMatch | `FreeTyv -> soft_failure ApplyMatchFailure
  | `Match mv ->
    let subst = Term.Match.to_subst mv in

    let goals = List.map (Term.subst subst) subs in
    List.map (fun g -> TS.set_goal g s) goals

(** [apply_in f hyp s] tries to match a premise of [f] with the conclusion of
    [hyp], and replaces [hyp] by the conclusion of [f].
    It generates a new subgoal for any remaining premises of [f], plus all
    premises of the original [hyp].

    E.g., if `H1 : A -> B` and `H2 : A` then `apply H1 in H2` replaces
    `H2 : A` by `H2 : B`
*)
let apply_in (pat : Term.message Term.pat) (hyp : Ident.t) (s : TS.t) 
  : TS.t list =
  let fprems, fconcl = Term.decompose_impls_last pat.pat_term in

  let h = Hyps.by_id hyp s in
  let hprems, hconcl = Term.decompose_impls_last h in

  let try1 fprem =
    if not (Vars.Sv.subset pat.pat_vars (Term.fv fprem)) then None
    else
      let pat = { pat with pat_term = fprem } in

      match Term.Match.try_match hconcl pat with
      | `NoMatch | `FreeTyv -> None
      | `Match mv -> Some mv
  in

  (* try to match a premise of [form] with [hconcl] *)
  let rec find_match acc fprems = match fprems with
    | [] -> None
    | fprem :: fprems ->
      match try1 fprem with
      | None -> find_match (fprem :: acc) fprems
      | Some mv ->
        (* premises of [form], minus the matched premise *)
        let fprems_other = List.rev_append acc fprems in
        Some (fprems_other, mv)
  in

  match find_match [] fprems with
  | None -> soft_failure ApplyMatchFailure
  | Some (fsubgoals,mv) ->
    let subst = Term.Match.to_subst mv in

    (* instantiate the inferred variables everywhere *)
    let fprems_other = List.map (Term.subst subst) fsubgoals in
    let fconcl = Term.subst subst fconcl in

    let goal1 =
      let s = Hyps.remove hyp s in
      Hyps.add (Args.Named (Ident.name hyp)) fconcl s
    in

    List.map (fun prem ->
        TS.set_goal prem s
      ) (hprems @               (* remaining premises of [hyp] *)
         fprems_other)          (* remaining premises of [form] *)
    @
    [goal1]


(** Parse apply tactic arguments *)
let p_apply_args (args : Args.parser_arg list) (s : TS.sequent) :
  TS.t list * Term.message Term.pat * LT.target =
  let subgoals, pat, in_opt =
    match args with
    | [Args.ApplyIn (Theory.PT_hol pt,in_opt)] ->
      let _, pat = LT.convert_pt_hol pt s in
      [], pat, in_opt

    | [Args.ApplyIn (Theory.PT_form f,in_opt)] ->
      begin
        match LT.convert_args s args Args.(Sort Boolean) with
        | Args.Arg (Boolean f) ->
          let subgoal = TS.set_goal f s in
          let pat = Term.pat_of_form f in
          [subgoal], pat, in_opt

        | _ -> bad_args ()
      end

    | _ -> bad_args ()
  in

  let target = match in_opt with
    | Some lsymb -> LT.T_hyp (fst (Hyps.by_name lsymb s))
    | None       -> LT.T_goal
  in
  subgoals, pat, target


let apply_tac_args (args : Args.parser_arg list) s : TS.t list =
  let subgoals, pat, target = p_apply_args args s in
  match target with
  | LT.T_goal    -> subgoals @ apply pat s      
  | LT.T_hyp id  -> subgoals @ apply_in pat id s 
  | LT.T_felem _ -> assert false

let apply_tac args = LT.wrap_fail (apply_tac_args args)

let () =
  T.register_general "apply"
    ~tactic_help:{
      general_help=
        "Matches the goal with the conclusion of the formula F provided \
         (directly, using lemma, or using an axiom), trying to instantiate \
         F variables. Creates one subgoal for each premises of F.\n\
         Usage: apply my_lem.\n       \
         apply my_axiom.\n       \
         apply (forall (x:message), F => G).";
      detailed_help="";
      usages_sorts=[];
      tactic_group=Structural}
    apply_tac

(*------------------------------------------------------------------*)
let rec do_intros_ip (intros : Args.intro_pattern list) s =
  match intros with
  | [] -> [s]

  | (Args.SItem s_item) :: intros ->
    do_intros_ip_list intros (do_s_item s_item s)

  | (Args.Simpl s_ip) :: intros ->
    let ss = do_intro_pat s_ip s in
    do_intros_ip_list intros ss

  | (Args.SExpnd s_e) :: intros ->
    let ss = LT.do_rw_item (s_e :> Args.rw_item) `Goal s in
    let ss = as_seq1 ss in (* we get exactly one new goal *)
    do_intros_ip intros ss

  | (Args.StarV loc) :: intros0 ->
    let repeat, s =
      try
        let handler, s = do_intro_var s in
        true, do_naming_pat handler Args.AnyName s

      with Tactics.Tactic_soft_failure (_,NothingToIntroduce) ->
        false, s
    in
    let intros = if repeat then intros else intros0 in
    do_intros_ip intros s

  | (Args.Star loc) :: intros ->
    try
      let handler, s = do_intro s in
      let s = do_naming_pat handler Args.AnyName s in
      do_intros_ip [Args.Star loc] s

    with Tactics.Tactic_soft_failure (_,NothingToIntroduce) -> [s]


and do_intros_ip_list intros ss = List.concat_map (do_intros_ip intros) ss

let intro_tac_args args s =
  match args with
  | [Args.IntroPat intros] -> do_intros_ip intros s
  | _ -> bad_args ()

let intro_tac args = LT.wrap_fail (intro_tac_args args)

let () =
  T.register_general "intro"
    ~tactic_help:{general_help = "Introduce topmost connectives of conclusion \
                                  formula, when it can be done in an invertible, \
                                  non-branching fashion.\
                                  \n\nUsage: intro a b _ c *";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    intro_tac


(*------------------------------------------------------------------*)
(** Projecting a goal on a bi-system
  * to distinct goals for each projected system. *)

let project s =
  let system = TS.system s in
  match system with
  | Single _ ->
    soft_failure (Tactics.Failure "goal already deals with a \
                                           single process")
  | _ ->
    let s1 = TS.set_system
        SystemExpr.(project_system PLeft  system) s in
    let s2 = TS.set_system
        SystemExpr.(project_system PRight system) s in
    let s1 = TS.pi PLeft s1 in
    let s2 = TS.pi PRight s2 in
    [s1;s2]

let () =
  T.register "project"
     ~tactic_help:{
       general_help = "Turn a goal on a bi-system into one goal for each system.";
       detailed_help = "Essentially, this is a function application on the \
                        diff operator.";
       usages_sorts = [Sort None];
       tactic_group = Structural}
     project

(*------------------------------------------------------------------*)
(** Replacing a conditional by the then branch (resp. the else branch) if the
 * condition is true (resp. false). *)

let apply_yes_no_if b s =
  let cntxt = TS.mk_trace_cntxt s in
  let conclusion = TS.goal s in
  (* search for the first occurrence of an if-then-else in [elem] *)
  match Iter.get_ite_term cntxt conclusion with
  | [] ->
    soft_failure
      (Tactics.Failure
         "the conclusion must contain at least \
          one occurrence of an if term")

  | occ :: _ ->
    (* Context with bound variables (eg try find) are not supported. *)
    if not (Sv.is_empty occ.Iter.occ_vars) then
      soft_failure (Tactics.Failure "cannot be applied in a under a binder");

    let c,t,e = occ.occ_cnt in

    let branch, trace_sequent =
      if b then (t, TS.set_goal c s)
      else (e, TS.set_goal (Term.mk_not c) s)
    in
    let subst = [Term.ESubst (Term.mk_ite c t e,branch)] in
    [ trace_sequent; TS.subst subst s ]

let yes_no_if b =
  (function
    | [] ->
      fun s sk fk -> begin match apply_yes_no_if b s with
        | subgoals -> sk subgoals fk
        | exception Tactics.Tactic_soft_failure e -> fk e
      end
    | _ -> hard_failure (Tactics.Failure "no argument allowed"))

let () =
  T.register "yesif"
    ~tactic_help:{
      general_help = "Replaces the first conditional in \
                      the conclusion by its then branch if the \
                      condition is true.";
      detailed_help = "Replaces a proof goal with conclusion `if phi \
                       then u else v` by the goals 'phi <=> true' \
                       and the original goal now with u instead of \
                       the conditional.";
      usages_sorts = [Sort None];
      tactic_group = Structural}
    (apply_yes_no_if true)

let () =
  T.register "noif"
    ~tactic_help:{
      general_help = "Replaces the first conditional in \
                      the conclusion by its else branch if the \
                      condition is false.";
      detailed_help = "Replaces a proof goal with condition `if phi \
                       then u else v` by the goals 'phi <=> false' \
                       and the original goal now with v instead of \
                       the conditional.";
      usages_sorts = [Sort None];
      tactic_group = Structural}
    (apply_yes_no_if false)


(*------------------------------------------------------------------*)
(** {2 Cryptographic Tactics} *)

(*------------------------------------------------------------------*)
(** Unforgeability Axioms *)

type unforgeabiliy_param = Term.fname * Term.nsymb * Term.message
                           * Term.message
                           * (Symbols.fname Symbols.t -> bool)
                           * Term.message list * bool
                           * (Symbols.fname Symbols.t -> bool) option

let euf_param table (t : Term.message) : unforgeabiliy_param =
  let bad_param () =
    soft_failure
      (Tactics.Failure
         "euf can only be applied to an hypothesis of the form h(t,k)=m \
          or checksign(s,pk(k))=m \
          for some hash or signature or decryption functions") in

  let at = match t with
    | Atom (`Message at) -> at
    | _ -> bad_param () in

  match at with
  | (`Eq, Fun ((checksign, _),    _, [s; Fun ((pk,_), _, [Name key])]), m)
  | (`Eq, m, Fun ((checksign, _), _, [s; Fun ((pk,_), _, [Name key])])) ->
    begin match Theory.check_signature table checksign pk with
      | None ->
        soft_failure
          (Failure "the message must be a signature check with \
                    the associated pk")

      | Some sign -> (sign, key, m, s,  (fun x -> x=pk), [], true, None)
    end

  | (`Eq, Fun ((hash, _), _, [m; Name key]), s)
    when Symbols.is_ftype hash Symbols.Hash table ->
    (hash, key, m, s, (fun x -> false), [], true, None)

  | (`Eq, s, Fun ((hash, _), _, [m; Name key]))
    when Symbols.is_ftype hash Symbols.Hash table ->
    (hash, key, m, s, (fun x -> false), [], true, None)

  | _ -> bad_param ()

let intctxt_param table (t : Term.message) : unforgeabiliy_param =
  let bad_param () =
    soft_failure
      (Tactics.Failure
         "intctxt can only be applied to an hypothesis of the form \
          sdec(s,sk) <> fail \
          or sdec(s,sk) = m (or symmetrically) \
          for some hash or signature or decryption functions") in

  let at = match t with
    | Atom (`Message at) -> at
    | _ -> bad_param () in

  let param_dec sdec key m s =
    match Symbols.Function.get_data sdec table with
    | Symbols.AssociatedFunctions [senc] ->
      (senc, key, m, s,  (fun x -> x = sdec),
       [ (Term.Atom (`Message (`Eq, s, Term.mk_fail)))], false, None)
    | Symbols.AssociatedFunctions [senc; h] ->
      (senc, key, m, s,  (fun x -> x = sdec || x = h),
       [ (Term.Atom (`Message (`Eq, s, Term.mk_fail)))], false, None)

    | _ -> assert false in

  match at with
  | (`Eq, Fun ((sdec, _), _, [m; Name key]), s)
    when Symbols.is_ftype sdec Symbols.SDec table ->
    param_dec sdec key m s

  | (`Eq, s, Fun ((sdec, is), _, [m; Name key]))
    when Symbols.is_ftype sdec Symbols.SDec table ->
    param_dec sdec key m s

  | (`Neq, (Fun ((sdec, _), _, [m; Name key]) as s), Fun (fail, _, _))
    when Symbols.is_ftype sdec Symbols.SDec table && fail = Term.f_fail->
    param_dec sdec key m s

  | (`Neq, Fun (fail, _, _), (Fun ((sdec, is), _, [m; Name key]) as s))
    when Symbols.is_ftype sdec Symbols.SDec table && fail = Term.f_fail ->
    param_dec sdec key m s

  | _ -> bad_param ()




let euf_apply_schema sequent (_, key, m, s, _, _, _, _) case =
  let open Euf in

  (* Equality between hashed messages *)
  let new_f = Term.Atom (`Message (`Eq, case.message, m)) in

  (* Equalities between key indices *)
  let eq_indices =
    List.fold_left2
      (fun cnstr i i' ->
         Term.mk_and cnstr (Term.Atom (`Index (`Eq, i, i'))))
      Term.mk_true
      key.s_indices case.key_indices
  in

  let system = TS.system sequent in
  let table  = TS.table sequent in

  (* Now, we need to add the timestamp constraints. *)
  (* The action name and the action timestamp variable are equal. *)
  let action_descr_ts =
    SystemExpr.action_to_term table system case.action_descr.Action.action
  in
 let ts_list =
    let iter = new Fresh.get_actions ~cntxt:(TS.mk_trace_cntxt sequent) in
    List.iter iter#visit_message [s; m];
    iter#get_actions
  in
  (* The action occured before the test H(m,k) = s. *)
  let maximal_elems = TS.maximal_elems ~precise:false sequent ts_list in

  let le_cnstr =
    List.map
      (function ts ->
        Term.Atom (Term.mk_timestamp_leq action_descr_ts ts))
      (maximal_elems)
  in
  let le_cnstr = Term.mk_ors le_cnstr in

  (* TODO: use an existential for new indices. *)
  let sequent = TS.set_env case.env sequent in

  let goal =
    Term.mk_impls [eq_indices; new_f; le_cnstr]
      (TS.goal sequent)
  in
  TS.set_goal goal sequent

let euf_apply_direct s (_, key, m, _, _, _, _, _) Euf.{d_key_indices;d_message} =
  (* The components of the direct case may feature variables that are
   * not in the current environment: this happens when the case is extracted
   * from under a binder, e.g. a Seq or ForAll construct. We need to add
   * such variables to the environment. *)
  let init_env = TS.env s in
  let subst,env =
    List.fold_left
      (fun (subst,env) (Vars.EVar v) ->
         if Vars.mem init_env v then subst,env else
         let env,v' = Vars.fresh env v in
         let subst = Term.(ESubst (Var v, Var v')) :: subst in
         subst,env)
      ([],init_env)
      (List.sort_uniq Stdlib.compare
         (List.map (fun i -> Vars.EVar i) d_key_indices @
          Term.get_vars d_message))
  in
  let s = TS.set_env env s in
  let d_message = Term.subst subst d_message in

  (* Equality between hashed messages. *)
  let eq_hashes = Term.Atom (`Message (`Eq, d_message, m)) in

  (* Equality between key indices. *)
  let eq_indices =
    List.fold_left2
      (fun cnstr i i' ->
         let i' = Term.subst_var subst i' in
         Term.mk_and ~simpl:false cnstr (Term.Atom (`Index (`Eq, i, i'))))
      Term.mk_true
      key.s_indices d_key_indices
  in

  let goal =
    Term.mk_impls [eq_indices; eq_hashes] (TS.goal s)
  in
  TS.set_goal goal s

let euf_apply_facts drop_head s
    ((head_fn, key, mess, sign, allow_functions, _, _, fun_wrap_key) as p) =
  let env = TS.env s in
  let cntxt = TS.mk_trace_cntxt s in

  (* check that the SSCs hold *)
  Euf.key_ssc ~messages:[mess;sign] ~allow_functions ~cntxt head_fn key.s_symb;

  (* build the rule *)
  let rule =
    Euf.mk_rule
      ~elems:[] ~drop_head ~allow_functions ~fun_wrap_key
      ~cntxt ~env ~mess ~sign
      ~head_fn ~key_n:key.s_symb ~key_is:key.s_indices
  in

  let schemata_premises =
    List.map (fun case -> euf_apply_schema s p case) rule.Euf.case_schemata

  and direct_premises =
    List.map (fun case -> euf_apply_direct s p case) rule.Euf.cases_direct
  in

  if Symbols.is_ftype head_fn Symbols.SEnc cntxt.table
  || Symbols.is_ftype head_fn Symbols.AEnc cntxt.table then
    Cca.check_encryption_randomness
      cntxt
      rule.Euf.case_schemata rule.Euf.cases_direct head_fn [mess;sign] [];

  schemata_premises @ direct_premises

(** Tag EUFCMA - for composition results *)
let euf_apply
    (get_params : Symbols.table -> Term.message -> unforgeabiliy_param)
    (Args.String hyp_name)
    (s : TS.t) =
  let table = TS.table s in
  let id, at = Hyps.by_name hyp_name s in


  let (h,key,m,_,_,extra_goals,drop_head,_) as p = get_params table at in
  let extra_goals = List.map (fun x ->
      TS.set_goal (Term.mk_impl x (TS.goal s)) s
    ) extra_goals in

  let tag_s =
    let f =
      Prover.get_oracle_tag_formula (Symbols.to_string h)
    in
    (* if the hash is not tagged, the formula is False, and we don't create
       another goal. *)
    if f = Term.mk_false
    then []
    else
      (* else, we create a goal where m,sk satisfy the axiom *)
      let (Vars.EVar uvarm),(Vars.EVar uvarkey),f = match f with
        | ForAll ([uvarm;uvarkey],f) -> uvarm,uvarkey,f
        | _ -> assert false
      in
      match Vars.ty uvarm,Vars.ty uvarkey with
      | Type.(Message, Message) -> let f = Term.subst [
          ESubst (Term.Var uvarm,m);
          ESubst (Term.Var uvarkey,Term.Name key);] f in
        [TS.set_goal
           (Term.mk_impl f (TS.goal s)) s]
      | _ -> assert false in

  (* we create the honest sources using the classical eufcma tactic *)
  try
    let honest_s = euf_apply_facts drop_head s p in
    (tag_s @ honest_s @ extra_goals)
  with Euf.Bad_ssc -> soft_failure Tactics.Bad_SSC

let () =
  T.register_typed "euf"
    ~general_help:"Apply the euf axiom to the given hypothesis name."
    ~detailed_help:"If the hash has been declared with a tag formula, applies \
                    the tagged version.  given tag. Tagged eufcma, with a tag T, \
                    says that, under the syntactic side condition, a hashed \
                    message either satisfies the tag T, or was honestly \
                    produced. The tag T must refer to a previously defined axiom \
                    f(mess,sk), of the form forall (m:message,sk:message)."
    ~tactic_group:Cryptographic
    (euf_apply euf_param) Args.String

let () =
  T.register_typed "intctxt"
    ~general_help:"Apply the intctxt axiom to the given hypothesis name."
    ~detailed_help:"Conditions are similar to euf."
    ~tactic_group:Cryptographic
    (euf_apply intctxt_param) Args.String



let non_malleability_param table (t : Term.message) : unforgeabiliy_param =
  let bad_param () =
    soft_failure
      (Tactics.Failure
         "NM can only be applied to an hypothesis of the form
          sdec(s,sk) = m (or symmetrically) ") in

  let at = match t with
    | Atom (`Message at) -> at
    | _ -> bad_param () in

  let param_dec adec key m s =
    match Symbols.Function.get_data adec table with
    | Symbols.AssociatedFunctions [aenc; pk] ->
      (aenc, key, m, s,  (fun x -> x = adec || x = pk),
       [ ], false, Some (fun x -> x=pk))

    | _ -> assert false in

  match at with
  | (`Eq, Fun ((adec, _), _, [m; Name key]), s)
    when Symbols.is_ftype adec Symbols.ADec table ->
    param_dec adec key m s

  | (`Eq, s, Fun ((adec, _), _, [m; Name key]))
    when Symbols.is_ftype adec Symbols.ADec table ->
    param_dec adec key m s

  | _ -> bad_param ()


exception Name_not_hidden

class name_under_enc (cntxt:Constr.trace_cntxt) enc is_pk target_n key_n
  = object (self)

 inherit Iter.iter_approx_macros ~exact:false ~cntxt as super

 method visit_message t =
    Printer.pr "test: %a" Term.pp t;
    match t with
    (* any name n can occur as enc(_,_,pk(k)) *)
    | Term.Fun ((f, _), _, [_; m; Term.Fun ((g,_), _ , [Term.Name k]) ])
      when f = enc && is_pk g && k.s_symb = key_n->  super#visit_message m
    | Term.Name name when name.s_symb = target_n -> raise Name_not_hidden
    | Term.Var m -> raise Name_not_hidden

    | _ -> super#visit_message t

end


let non_malleability Args.(Pair (String hyp_name, Opt (Message, opt_m))) (s : TS.t) =
  let enc_occurences_goals =
    euf_apply non_malleability_param (Args.String hyp_name) s in
  let table = TS.table s in
  let id, at = Hyps.by_name hyp_name s in
  let (enc, key_n, _, mess1, mess2 , _ , _, is_pk) = non_malleability_param table at in
  let name_ssc =  match mess1, opt_m with
    | Term.Name name, None -> name
    | m, Some (Message (Term.Name name,ty)) -> name
    | _, _ -> soft_failure
      (Tactics.Failure
         "When NM is applied to an hypothesis of the form
          sdec(s,sk) = m, where m is not a name, one must give as extra \
          parameter a name such that m strongly depends on it. ")
  in
  (* we check is the given name name_ssc only occurs under valid encryptions *)
  (* the fact that the encryptions all use distinct randoms is checked by
     the later euf application (cf euf_apply_facts) *)
  let is_pk = match is_pk with Some f -> f | _ -> assert false in
  let cntxt = TS.mk_trace_cntxt s in
  let ssc =
    new name_under_enc cntxt enc is_pk name_ssc.s_symb key_n.s_symb in
  (try
     (* Remark: if we start considering C[dec(m,sk)], we will need to also
        check the SSC for C. *)
     SystemExpr.(iter_descrs cntxt.table cntxt.system
                   (fun action_descr ->
                      ssc#visit_message (snd action_descr.output) ;
                      List.iter (fun (_,t) -> ssc#visit_message t) action_descr.updates))
   with Name_not_hidden -> soft_failure
                             Tactics.NameNotUnderEnc
  );
  let neq_goals = match mess1, opt_m with
    | Term.Name name, None -> [] (* we have nothing to do, a name will always be
                                    not equal to another fres name *)
  | m, Some (Message (Term.Name n as name,ty)) ->
    (* we now create the inequality to be checked *)
    let ndef = Symbols.{ n_iarr = 0; n_ty = ty; } in
    let table,n =
      Symbols.Name.declare table (L.mk_loc L._dummy "n_NM") ndef
    in
    let freshname = Term.mk_isymb n ty [] in
    let s = TS.set_table table s in
    let new_mess = Term.subst [Term.ESubst (name, Term.Name freshname)] m in
    [TS.set_goal (Term.Atom (`Message (`Neq, new_mess, m))) s]
  | _, _ -> soft_failure
      (Tactics.Failure
         "When NM is applied to an hypothesis of the form
          sdec(s,sk) = m, where m is not a name, one must give as extra \
          parameter a name such that m strongly depends on it. ")
    in
  neq_goals @ enc_occurences_goals

let () =
  T.register_typed "nm"
    ~general_help:"Apply the NM axiom to the given hypothesis name."
    ~detailed_help:"Can be applied to any hypothesis of the form dec(m,sk) = t(n)."
    ~tactic_group:Cryptographic
    non_malleability Args.(Pair (String, Opt Message))

(*------------------------------------------------------------------*)
let valid_hash (cntxt : Constr.trace_cntxt) (t : Term.message) =
  match t with
  | Fun ((hash, _), _, [m; Name key]) ->
    Symbols.is_ftype hash Symbols.Hash cntxt.table
    && Euf.check_key_ssc
      ~allow_vars:true ~messages:[m] ~allow_functions:(fun x -> false)
      ~cntxt hash key.s_symb

  | _ -> false

(** We collect all hashes appearing inside the hypotheses, and which satisfy
    the syntactic side condition. *)
let top_level_hashes s =
  let cntxt = TS.mk_trace_cntxt s in

  let hashes =
    List.filter (valid_hash cntxt) (TS.get_all_messages s)
    |> List.sort_uniq Stdlib.compare
  in

  if List.length hashes = 0 then soft_failure Tactics.NoSSC;

  let rec make_eq acc hash_list =
    match hash_list with
    | [] -> acc
    | h1::q ->
      List.fold_left
        (fun acc h2 ->
           match h1, h2 with
           | Fun (hash1, _, [_; Name key1]),
             Fun (hash2, _, [_; Name key2])
             when hash1 = hash2 && key1 = key2 -> (h1, h2) :: acc
           | _ -> acc)
        (make_eq acc q) q
  in

  let trs = TS.get_trs s in

  make_eq [] hashes
  |> List.filter (fun (a,b) ->
      Completion.check_equalities trs [Term.ESubst (a,b)])



(** [collision_resistance judge sk fk] applies the collision resistance axiom
    between the hashes:
    - if [i = Some j], collision in hypothesis [j]
    - if [i = None], collects all equalities between hashes that occur at
    toplevel in message hypotheses. *)
let collision_resistance TacticsArgs.(Opt (String, i)) (s : TS.t) =

  let hash_eqs = match i with
    | None -> top_level_hashes s
    | Some (String j) -> match Hyps.by_name j s with
      | _, Term.Atom (`Message (`Eq, t1, t2)) ->
        let cntxt = TS.mk_trace_cntxt s in
        if not (valid_hash cntxt t1) || not (valid_hash cntxt t2) then
          soft_failure Tactics.NoSSC;

        [t1,t2]
      | _ -> soft_failure Tactics.NoCollision
  in

  let new_facts =
    List.fold_left
      (fun acc (h1,h2) ->
         match h1, h2 with
         | Fun ((hash1, _), _, [m1; Name key1]),
           Fun ((hash2, _), _, [m2; Name key2])
           when hash1 = hash2 && key1 = key2 ->
           Term.Atom (`Message (`Eq, m1, m2)) :: acc
         | _ -> acc)
      [] hash_eqs
  in
  let f_coll = Term.mk_ands new_facts in

  if f_coll = Term.mk_true then soft_failure Tactics.NoCollision;

  let goal = Term.mk_impl ~simpl:false f_coll (TS.goal s) in
  [TS.set_goal goal s]

let () = T.register_typed "collision"
    ~general_help:"Collects all equalities between hashes \
                   occurring at toplevel in\
                   message hypotheses, and adds the equalities \
                   between messages that have the same hash with \
                   the same valid key."
    ~detailed_help:"A key is valid if it is only used in a key \
                    position. Remark that this could be relaxed, \
                    as CR holds for any valid key, even known to \
                    the attacker."
    ~tactic_group:Cryptographic
    collision_resistance Args.(Opt String)
