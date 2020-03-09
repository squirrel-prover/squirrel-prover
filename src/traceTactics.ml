open Tactics
open Atom

open Term

type tac = TraceSequent.t Tactics.tac

module T = Prover.TraceTactics

(** Propositional connectives *)

(** Reduce a goal with a disjunction conclusion into the goal
  * where the conclusion has been replace with the first disjunct. *)
let goal_or_right_1 (s : TraceSequent.t) sk fk =
  match TraceSequent.get_conclusion s with
  | (Or (lformula, _)) -> sk [TraceSequent.set_conclusion (lformula) s] fk
  | _ -> fk (Tactics.Failure "Cannot introduce a disjunction")

(** Reduce a goal with a disjunction conclusion into the goal
  * where the conclusion has been replace with the second disjunct. *)
let goal_or_right_2 (s : TraceSequent.t) sk fk =
  match TraceSequent.get_conclusion s with
  | (Or (_, rformula)) -> sk [TraceSequent.set_conclusion (rformula) s] fk
  | _ -> fk (Tactics.Failure "Cannot introduce a disjunction")

let () =
  T.register "left"
    ~help:"Reduce a goal with a disjunction conclusion into the goal where the \
       \n conclusion has been replaced with the first disjunct.\
           \n Usage: left."
    goal_or_right_1 ;
  T.register "right"
    ~help:"Reduce a goal with a disjunction conclusion into the goal where the \
           \n conclusion has been replace with the second disjunct.\
           \n Usage: right."
    goal_or_right_2

let goal_true_intro (s : TraceSequent.t) sk fk =
  match TraceSequent.get_conclusion s with
  | True -> sk [] fk
  | _ -> fk (Tactics.Failure "Cannot introduce true")

let () =
  T.register "true" ~help:"Concludes if the goal is true.\n Usage: true."
    goal_true_intro

(** Split a conjunction conclusion,
  * creating one subgoal per conjunct. *)
let goal_and_right (s : TraceSequent.t) sk fk =
  match TraceSequent.get_conclusion s with
  | And (lformula, rformula) ->
    sk [ TraceSequent.set_conclusion (lformula) s;
         TraceSequent.set_conclusion (rformula) s ] fk
  | _ -> fk (Tactics.Failure "Cannot introduce a conjonction")

let () =
  T.register "split"
    ~help:"Split a conjunction conclusion, creating one subgoal per conjunct.\
           \n Usage: split."
    goal_and_right

(** Compute the goal resulting from the addition of a list of
  * formulas as hypotheses,
  * followed by the left intro of existentials and conjunctions. *)
let rec left_introductions s = function
  | Term.And (f,g) :: l -> left_introductions s (f::g::l)
  | Term.Exists (vars,f) :: l ->
      let env = TraceSequent.get_env s in
      let subst,env =
        List.fold_left
          (fun (subst,env) (Vars.EVar v) ->
             let env,v' =
               Vars.make_fresh env (Vars.sort v) (Vars.name v)
             in
             let item = Term.ESubst (Var v, Var v') in
             item::subst, env)
          ([],env)
          vars
      in
      let f = Term.subst subst f in
        left_introductions (TraceSequent.set_env env s) (f::l)
  | f :: l -> left_introductions (TraceSequent.add_formula f s) l
  | [] -> s

let left_intros hyp_name s sk fk =
  match TraceSequent.select_formula_hypothesis hyp_name s ~remove:true with
    | s,formula -> sk [left_introductions s [formula]] fk
    | exception Not_found -> fk (Tactics.Failure "no such hypothesis")

let () =
  T.register_general "introsleft"
    ~help:"Simplify conjonctions and existentials in an hypothesis.\
           \n Usage: notleft H."
    (function
      | [Prover.Theory (Theory.Var h)] -> left_intros h
      | _ -> raise @@ Tactics.Tactic_hard_failure
          (Tactics.Failure "improper arguments"))

let left_not_intro hyp_name s sk fk =
  let s,formula = TraceSequent.select_formula_hypothesis hyp_name s ~remove:true in
  let rec not_f = function
    | Exists (vs, f) -> ForAll(vs, not_f f)
    | ForAll (vs, f) -> Exists(vs, not_f f)
    | And (a, b) -> Or (not_f a, not_f b)
    | Or (a, b) -> And (not_f a, not_f b)
    | Impl (a, b) -> And(a, not_f b)
    | True -> False
    | False -> True
    | Not f -> f
    | Atom (#message_atom as a) -> Atom (Atom.not_message_atom a :> generic_atom)
    | Atom (#trace_atom as a) -> Atom (Atom.not_trace_atom a :> generic_atom)
    | m -> Not m
  in
  match formula with
  | Not f -> sk [TraceSequent.add_formula (not_f f) s] fk
  | _ -> raise @@ Tactics.Tactic_hard_failure
          (Tactics.Failure "Can only be applied to a negation formula.")

let () =
  T.register_general "notleft"
    ~help:"Push a negation inside a formula.\
           \n Usage: notleft H."
    (function
      | [Prover.Theory (Theory.Var h)] -> left_not_intro h
      | _ -> raise @@ Tactics.Tactic_hard_failure
          (Tactics.Failure "improper arguments"))


let timestamp_case ts s sk fk =
  let f = ref (Atom (`Timestamp (`Eq,ts,Term.Init))) in
  let add_action a =
    let indices =
      let env = ref @@ TraceSequent.get_env s in
      List.map
        (fun i -> Vars.make_fresh_from_and_update env i)
        a.Action.indices
    in
    let subst =
      List.map2 (fun i i' -> Term.ESubst (Term.Var i,Term.Var i'))
        a.Action.indices indices
    in
    let name = Action.to_term (Action.subst_action subst a.Action.action) in
    let case =
      let at = Term.Atom ((`Timestamp (`Eq,ts,name)) :> generic_atom) in
      let at = Term.subst subst at in
      if indices = [] then at else
        Exists (List.map (fun x -> Vars.EVar x) indices,at)
    in
    f := Term.Or (case,!f)
  in
  let system_id = TraceSequent.system_id s in
  Action.iter_descrs ~system_id add_action ;
  sk [TraceSequent.add_formula !f s] fk

let hypothesis_case hypothesis_name (s : TraceSequent.t) sk fk =
  let s,f = TraceSequent.select_formula_hypothesis hypothesis_name s ~remove:true in
  let rec disjunction_to_list acc = function
    | Or (f,g) :: l -> disjunction_to_list acc (f::g::l)
    | f :: l -> disjunction_to_list (f::acc) l
    | [] -> acc
  in
  let formulas = disjunction_to_list [] [f] in
  if List.length formulas = 1 then
    raise @@
    Tactics.Tactic_hard_failure
      (Tactics.Failure "Can only be applied to a disjunction.") ;
  sk (List.rev_map (fun f -> TraceSequent.add_formula f s ) formulas) fk

let case th s sk fk =
  (* if the conversion to a timestamp of the variable is successful, we perform
     a timestamp_case. If it fails, we try with hypothesis case. *)
    let tsubst = Theory.subst_of_env (TraceSequent.get_env s) in
    match Theory.convert tsubst th Sorts.Timestamp with
    | exception _ ->
      begin
        match th with
        | Theory.Var m -> hypothesis_case m s sk fk
        | _ -> raise @@ Tactics.Tactic_hard_failure
            (Tactics.Failure "improper arguments")
      end
    | ts -> timestamp_case ts s sk fk

let () =
  T.register_general "case"
    ~help:"When T is a timestamp variable, introduce a disjunction \
           \n hypothesis expressing the various forms that it could take. \
           \n when T is a disjunction name, split the given disjunction on the \
           \n left, creating corresponding subgoals.\
           \n Usage: case T."
    (function
       | [Prover.Theory th] -> case th
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))


let depends t1 t2 s sk fk =
  let tsubst = Theory.subst_of_env (TraceSequent.get_env s) in
  let a1, a2 =
    try
      Theory.convert tsubst t1 Sorts.Timestamp,
      Theory.convert tsubst t2 Sorts.Timestamp
    with _ -> raise @@ Tactics.Tactic_hard_failure
          (Tactics.Failure "arguments must be timestamps")
  in
  match a1, a2 with
  | Term.Action( n1, is1), Term.Action (n2, is2) ->
    if Action.(depends (of_term n1 is1) (of_term n2 is2)) then
      let atom = (Atom (`Timestamp (`Lt,a1,a2))) in
      sk [TraceSequent.add_formula atom s] fk
    else
      fk (Tactics.Failure "the second action does not depend on the first one")
  | _ -> raise @@ Tactics.Tactic_hard_failure
      (Tactics.Failure "arguments must be actions.")

let () =
  T.register_general "depends"
    ~help:"If the second action given as argument depends on the first action,\
           \n add the corresponding timestamp inequality.\
           \n Usage: depends a1 a2."
    (function
       | [Prover.Theory t1; Prover.Theory t2] -> depends t1 t2
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))

let false_left s sk fk =
  try
    let _ =
      TraceSequent.find_formula_hypothesis (function False -> true | _ -> false) s
    in
    sk [] fk
  with Not_found -> fk @@ Tactics.Failure "no False assumption"

let () =
  T.register_general "false_left"
    ~help:"Closes a goal when False is among its assumptions.\
           \n Usage: false_left."
    (function
       | [] -> false_left
       | _ -> raise @@ Tactics.Tactic_hard_failure
                         (Tactics.Failure "no argument allowed"))

(** [goal_intro judge sk fk] perform one introduction, either of a forall
    quantifier or an implication. Else, it returns [fk] *)
let goal_intro (s : TraceSequent.t) sk fk =
  match TraceSequent.get_conclusion s with
  | ForAll (vs,f) ->
    let env = ref (TraceSequent.get_env s) in
    let subst =
      List.map
        (fun (Vars.EVar x) ->
           Term.ESubst (Term.Var x,
                        Term.Var (Vars.make_fresh_from_and_update env x)))
        vs
    in
    let new_formula = Term.subst subst f in
    let new_judge = TraceSequent.set_conclusion new_formula s
                    |> TraceSequent.set_env (!env)
    in
    sk [new_judge] fk
  | Impl(lhs,rhs)->
    let s' =
      TraceSequent.add_formula lhs (TraceSequent.set_conclusion rhs s) in
    sk [s'] fk
  | Not f ->
    sk [TraceSequent.set_conclusion False s |> TraceSequent.add_formula f] fk
  | Atom (`Message (`Neq,u,v)) ->
    let h = `Message (`Eq,u,v) in
    let s' = TraceSequent.set_conclusion False s |> TraceSequent.add_formula (Atom h) in
    sk [s'] fk
  | _ ->
      fk (Tactics.Failure
            "Can only introduce implication, universal quantifications \
             \n and disequality conclusions.")

let () =
  T.register "intro"
    ~help:"Perform one introduction, either of a forall quantifier or an \
           \n implication.\
           \n Usage: intro."
    goal_intro

(** Quantifiers *)

(** [goal_exists_intro judge ths] introduces the existentially
    quantified variables in the conclusion of the judgment,
    using [ths] as existential witnesses. *)
let goal_exists_intro ths (s : TraceSequent.t) sk fk =
  match TraceSequent.get_conclusion s with
  | Exists (vs,f) when List.length ths = List.length vs ->
    begin
    try
      let nu = Theory.parse_subst (TraceSequent.get_env s) vs ths in
      let new_formula = Term.subst nu f in
      sk [TraceSequent.set_conclusion new_formula s] fk
    with Theory.(Conv (Undefined x)) -> raise @@ Tactics.Tactic_hard_failure
        (Tactics.Undefined x)
  end
  | _ -> fk (Tactics.Failure "Cannot introduce an exists")

let () =
  T.register_general "exists"
    ~help:"Introduce the existentially quantified variables in the conclusion \
           \n of the judgment, using the arguments as existential witnesses. \
           \n Usage: exists t_1, t_2."
    (fun l ->
       let ths =
         List.map
           (function
              | Prover.Theory tm -> tm
              | _ -> raise @@ Tactic_hard_failure
                  (Tactics.Failure "Improper arguments"))
           l
       in
       goal_exists_intro ths)

let exists_left hyp_name s sk fk =
  let s,f = TraceSequent.select_formula_hypothesis hyp_name s ~remove:true in
    match f with
      | Exists (vs,f) ->
          let env = ref @@ TraceSequent.get_env s in
          let subst =
            List.map
              (fun (Vars.EVar v) ->
                 Term.ESubst  (Term.Var v,
                               Term.Var (Vars.make_fresh_from_and_update env v))
              )
              vs
          in
          let f = Term.subst subst f in
          let s = TraceSequent.add_formula f (TraceSequent.set_env !env s) in
            sk [s] fk
      | _ -> fk @@ Tactics.Failure "Improper arguments"

let () =
  T.register_general "existsleft"
    ~help:"Introduce existential quantifier in hypothesis H.\
           \n Usage: existsleft H."
    (function
      | [Prover.Theory (Theory.Var h)] -> exists_left h
      | _ -> raise @@ Tactics.Tactic_hard_failure
          (Tactics.Failure "improper arguments"))

let simpl_left s sk fk =
  match
    TraceSequent.remove_formula_hypothesis
      (function
         | False | And _ | Exists _ -> true
         | _ -> false)
      s
  with
    | False, s' -> sk [] fk
    | And (f,g), s' ->
        sk
          [TraceSequent.add_formula f (TraceSequent.add_formula g s')]
          fk
    | Exists (vs,f), s' ->
        let env = ref @@ TraceSequent.get_env s in
        let subst =
          List.map
            (fun (Vars.EVar v) ->
               Term.ESubst  (Term.Var v,
                             Term.Var (Vars.make_fresh_from_and_update env v)))
            vs
        in
        let f = Term.subst subst f in
        let s = TraceSequent.add_formula f (TraceSequent.set_env !env s') in
          sk [s] fk
    | _ -> assert false
    | exception Not_found -> fk (Tactics.Failure "no such hypothesis")

let () =
  T.register "simpl_left"
    ~help:"Introduce all conjunctions, existentials and false hypotheses."
    simpl_left

let () =
  let open Tactics in
  let non_branching_intro =
    [ Abstract ("intro",[]) ;
      Abstract ("exists",[]) ;
      Abstract ("true",[]) ]
  in
  T.register_macro "intros"
    ~help:"Repeat intro.\n Usage: intros."
    (Repeat (OrElse non_branching_intro)) ;
  T.register_macro "anyintro"
    ~help:"Try any possible introduction.\n Usage: anyintro."
    (OrElse
       (Abstract ("split",[]) :: non_branching_intro))

(** Induction *)

let induction s sk fk =
  match TraceSequent.get_conclusion s with
  | ForAll ((Vars.EVar v)::vs,f) ->
    (match Vars.sort v with
       Sorts.Timestamp ->
       (
         (* We need two fresh variables in env,
          * but one will not be kept in the final environment. *)
         let env,v' = Vars.make_fresh_from (TraceSequent.get_env s) v in
         let _,v'' = Vars.make_fresh_from env v in
         (* Introduce v as v'. *)
         let f' = Term.subst [Term.ESubst (Term.Var v,Term.Var v')]
             (ForAll (vs,f))
         in
         (* Use v'' to form induction hypothesis. *)
         let (-->) a b = Impl (a,b) in
         let ih =
           ForAll ((Vars.EVar v'')::vs,
                   Atom (`Timestamp (`Neq,Term.Var v,Term.Init)) -->
                   (Atom (`Timestamp (`Lt,Term.Var v'',Term.Var v)
                            :> generic_atom) -->
                    Term.subst
                      [Term.ESubst (Term.Var v,Term.Var v'')] f))
         in
         let s =
           s
           |> TraceSequent.set_env env
           |> TraceSequent.set_conclusion f'
           |> TraceSequent.add_formula ~prefix:"IH" ih
         in
         sk [s] fk
       )
     | _ ->
       fk @@ Tactics.Failure
         "Conclusion must be an \
          universal quantification over a timestamp"
    )
  | _ ->
    fk @@ Tactics.Failure
      "Conclusion must be an \
       universal quantification over a timestamp"

let () = T.register "induction"
    ~help:"Apply the induction scheme to the conclusion.\
           \n Usage: induction."
    induction

(** [constraints judge sk fk] proves the sequent using its trace
  * formulas. *)
let constraints (s : TraceSequent.t) sk fk =
  let conclusions =
    try Term.disjunction_to_atom_list (TraceSequent.get_conclusion s)
    with Term.Not_a_disjunction -> []
  in
  let trace_conclusions =
    List.fold_left (fun acc (conc:Atom.generic_atom) -> match conc with
        | #trace_atom as a -> (Atom.not_trace_atom a)::acc
        | _ -> acc)
      []
      conclusions
  in
  let new_s = List.fold_left (fun s atom -> TraceSequent.add_formula
                                 (Term.Atom (atom :> generic_atom)) s)
      s
      trace_conclusions
  in
  if TraceSequent.constraints_valid new_s then
    sk [] fk
  else fk (Tactics.Failure "Constraints satisfiable")

let expand (term : Theory.term) (s : TraceSequent.t) sk fk =
  let tsubst = Theory.subst_of_env (TraceSequent.get_env s) in
  let system_id = TraceSequent.system_id s in

  let succ subst = sk [TraceSequent.apply_subst subst s] fk in

  match Theory.convert tsubst term Sorts.Boolean with
    | Macro ((mn, sort, is),l,a) ->
      succ [Term.ESubst (Macro ((mn, sort, is),l,a),
                         Macros.get_definition ~system_id sort mn is a)]
    | _ ->
      Tactics.hard_failure (Tactics.Failure "Can only expand macros")
    | exception Theory.(Conv (Type_error _)) ->
      begin
      match Theory.convert tsubst term Sorts.Message with
        | Macro ((mn, sort, is),l,a) ->
          succ [Term.ESubst (Macro ((mn, sort, is),l,a),
                             Macros.get_definition ~system_id sort mn is a)]
        | exception Theory.(Conv e) ->
          fk (Tactics.Failure  (Fmt.str "%a" Theory.pp_error e))
        | _ ->
          Tactics.hard_failure (Tactics.Failure "Can only expand macros")
    end
    | exception Theory.(Conv e) ->
      fk (Tactics.Failure  (Fmt.str "%a" Theory.pp_error e))

let () = T.register_general "expand"
    ~help:"Expand all occurences of the given macro inside the goal.\
           \n Usage: expand macro."
    (function
       | [Prover.Theory v1] -> expand v1
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))


(** [congruence judge sk fk] try to close the goal using congruence, else
    calls [fk] *)
let congruence (s : TraceSequent.t) sk fk =
 let conclusions =
    try Term.disjunction_to_atom_list (TraceSequent.get_conclusion s)
    with Term.Not_a_disjunction -> []
  in
  let term_conclusions =
    List.fold_left (fun acc (conc:Atom.generic_atom) -> match conc with
        | #message_atom as a -> (Atom.not_message_atom a)::acc
        | _ -> acc)
      []
      conclusions
  in
  let s = List.fold_left (fun s atom -> TraceSequent.add_formula
                                 (Term.Atom (atom :> generic_atom)) s)
      s
      term_conclusions
  in
  if TraceSequent.message_atoms_valid s then
    sk [] fk
  else fk (Tactics.Failure "Equations satisfiable")

let () = T.register "congruence"
    ~help:"Tries to derive false from the messages equalities.\
           \n Usage: congruence."
    congruence

let () = T.register "constraints"
    ~help:"Tries to derive false from the trace formulas.\
           \n Usage: constraints."
    constraints

(** [assumption judge sk fk] proves the sequent using the axiom rule. *)
let assumption (s : TraceSequent.t) sk fk =
  if TraceSequent.is_hypothesis (TraceSequent.get_conclusion s) s then
      sk [] fk
  else
    fk (Tactics.Failure "Conclusion is not an hypothesis")

let () = T.register "assumption"
    ~help:"Search for the conclusion inside the hypothesis.\
           \n Usage: assumption."
    assumption

(** Utils *)

let mk_or_cnstr l = match l with
  | [] -> Term.False
  | [a] -> a
  | a :: l' ->
    let rec mk_c acc = function
      | [] -> acc
      | x :: l -> mk_c (Term.Or (x,acc)) l in
    mk_c a l'

let mk_and_cnstr l = match l with
  | [] -> Term.True
  | [a] -> a
  | a :: l' ->
    let rec mk_c acc = function
      | [] -> acc
      | x :: l -> mk_c (Term.And (x,acc)) l in
    mk_c a l'

(** Eq-Indep Axioms *)

(* We include here rules that are specialization of the Eq-Indep axiom. *)

(** Add index constraints resulting from names equalities, modulo the TRS.
    The judgment must have been completed before calling [eq_names]. *)
let eq_names (s : TraceSequent.t) sk fk =
  let s,trs = TraceSequent.get_trs s in
  let terms = TraceSequent.get_all_terms s in
  (* we start by collecting equalities between names implied by the indep axiom.
  *)
  let new_eqs = Completion.name_indep_cnstrs trs terms in
  let s =
    List.fold_left
      (fun s c ->
         TraceSequent.add_formula c s)
      s new_eqs
  in
  (* we now collect equalities between timestamp implied by equalities between
     names. *)
  let s,trs = TraceSequent.get_trs s in
  let cnstrs = Completion.name_index_cnstrs trs
      (TraceSequent.get_all_terms s)
  in
  let s =
    List.fold_left
      (fun s c ->
         TraceSequent.add_formula c s)
      s cnstrs
  in
  sk [s] fk

let () = T.register "eqnames"
    ~help:"Add index constraints resulting from names equalities, modulo the \
           \n known equalities.\
           \n Usage: eqnames."
    eq_names

(** Add terms constraints resulting from timestamp and index equalities. *)
let eq_trace (s : TraceSequent.t) sk fk =
  let s, ts_classes = TraceSequent.get_ts_equalities s in
  let ts_classes = List.map (List.sort_uniq Pervasives.compare) ts_classes in
  let ts_subst =
    let rec asubst e = function
        [] -> []
      | p::q -> Term.ESubst (p,e) :: (asubst e q)
    in
    List.map (function [] -> [] | p::q -> asubst p q) ts_classes
    |> List.flatten
  in
  let s, ind_classes = TraceSequent.get_ind_equalities s in
  let ind_classes = List.map (List.sort_uniq Pervasives.compare) ind_classes in
  let ind_subst =
    let rec asubst e = function
        [] -> []
      | p::q -> Term.ESubst (Term.Var p,Term.Var e) :: (asubst e q)
    in
    (List.map (function [] -> [] | p::q -> asubst p q) ind_classes)
    |> List.flatten
  in
  let terms = TraceSequent.get_all_terms s in
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
    List.fold_left
      (fun s c ->
         TraceSequent.add_formula c s)
      s facts
  in
  sk [s] fk

let () = T.register "eqtrace"
    ~help:"Add terms constraints resulting from timestamp and index equalities.\
           \n Usage: eqtrace."
    eq_trace

let substitute (v1) (v2) (s : TraceSequent.t) sk fk=
  let tsubst = Theory.subst_of_env (TraceSequent.get_env s) in
  let subst =
    match
      Theory.convert tsubst v1 Sorts.Timestamp,
      Theory.convert tsubst v2 Sorts.Timestamp
    with
    | ts1,ts2 ->
      let s, models = TraceSequent.get_models s in
      if Constr.query models [(`Timestamp (`Eq,ts1,ts2))] then
        [Term.ESubst (ts1,ts2)]
      else
        raise @@ Tactic_hard_failure
          (Tactics.NotEqualArguments)
    | exception _ ->
      match
        Theory.convert tsubst v1 Sorts.Message,
        Theory.convert tsubst v2 Sorts.Message
      with
      | m1,m2 ->
        let s,trs = TraceSequent.get_trs s in
        if Completion.check_equalities trs [(m1,m2)] then
          [Term.ESubst (m1,m2)]
      else
        raise @@ Tactic_hard_failure
          (Tactics.NotEqualArguments)
      | exception _ ->
        match Theory.conv_index tsubst v1, Theory.conv_index tsubst v2 with
        | i1,i2 ->
          let s, models = TraceSequent.get_models s in
          if Constr.query models [(`Index (`Eq,i1,i2))] then
            [Term.ESubst (Term.Var i1,Term.Var i2)]
          else
            raise @@ Tactic_hard_failure
              (Tactics.NotEqualArguments)
        | exception _ ->  raise @@ Tactic_hard_failure
            (Tactics.Failure "Improper arguments.")
  in
  sk [TraceSequent.apply_subst subst s] fk

let () =
  T.register_general "substitute"
    ~help:"If the seuqnet implies that the arguments i1, i2 are equals,\
           \n replaces all occurences of i1 by i2 inside the sequent.\
           \n Usage: substitute i1 i2."
    (function
       | [Prover.Theory v1; Prover.Theory v2] -> substitute v1 v2
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))


let exec a s sk fk =
  let tsubst = Theory.subst_of_env (TraceSequent.get_env s) in
  let a =
    try
      Theory.convert tsubst a Sorts.Timestamp
    with
    _ ->  raise @@ Tactics.Tactic_hard_failure
      (Tactics.Failure "improper arguments")
  in
  let var = snd Vars.(make_fresh empty_env Sorts.Timestamp "t") in
  let formula =
    ForAll (
      [Vars.EVar (var)],
      Impl(Atom (`Timestamp (`Leq,Var var,a)),
           Macro(Term.cond_macro,[],Var var)
          )
    )
  in
  sk [TraceSequent.add_formula formula s] fk

let () =
  T.register_general "executable"
    ~help:"Specify that the macro exec implis cond for all previous timestamps.\
           \n Usage: executable t."
    (function
       | [Prover.Theory v] -> exec v
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))


(** EUF Axioms *)

let euf_param (`Message at : message_atom) = match at with
  | (`Eq, Fun ((hash, _), [m; Name key]), s)
  | (`Eq, s, Fun ((hash, _), [m; Name key]))->
    if Theory.is_hash hash then
      (hash, key, m, s)
    else raise @@ Tactic_hard_failure
        (Tactics.Failure "The function symbol is not a hash function.")
  | _ -> raise @@ Tactic_hard_failure
      (Tactics.Failure
         "Euf can only be applied to hypothesis of the form h(t,k)=m.")

let euf_apply_schema sequent (_, (_, _), m, s) case =
  let open Euf in
  (* We create the term equality *)
  let new_f = Term.Atom (`Message (`Eq, case.message, m)) in
  (* Now, we need to add the timestamp constraints. *)
  (* The action name and the action timestamp variable are equal. *)
  let action_descr_ts = Action.to_term case.action_descr.Action.action in
  (* The action occured before the test H(m,k) = s. *)
  let le_cnstr =
    List.map
      (function
         | Pred ts ->
             Term.Atom (`Timestamp (`Lt, action_descr_ts, ts))
         | ts ->
             Term.Atom (`Timestamp (`Leq, action_descr_ts, ts)))
      (snd (TraceSequent.maximal_elems sequent (precise_ts s @ precise_ts m)))
    |> mk_or_cnstr
  in
  (new_f, le_cnstr, case.env)

let euf_apply_direct _ (_, (_, key_is), m, _) dcase =
  let open Euf in
  (* We create the term equality *)
  let eq = Term.Atom (`Message (`Eq, dcase.d_message, m)) in
  (* Now, we need to add the timestamp constraint between [key_is] and
     [dcase.d_key_indices]. *)
  let eq_cnstr =
    List.map2
      (fun i i' -> Term.Atom (`Index (`Eq, i, i')))
      key_is dcase.d_key_indices
    |> mk_and_cnstr
  in
  (eq, eq_cnstr)

let euf_apply_facts s at =
  let p = euf_param at in
  let env = TraceSequent.get_env s in
  let (hash_fn, (key_n, key_is), mess, sign) = p in
  let system_id = TraceSequent.system_id s in
  let rule = Euf.mk_rule ~system_id ~env ~mess ~sign ~hash_fn ~key_n ~key_is in
  let schemata_premises =
    List.map (fun case ->
        let new_f, new_cnstr, new_env = euf_apply_schema s p case in
        TraceSequent.add_formula new_f s
        |> TraceSequent.add_formula new_cnstr
        |> TraceSequent.set_env new_env
      ) rule.Euf.case_schemata
  and direct_premises =
    List.map (fun case ->
        let new_f, new_cnstr = euf_apply_direct s p case in
        TraceSequent.add_formula new_f s
        |> TraceSequent.add_formula new_cnstr
      ) rule.Euf.cases_direct
  in
  schemata_premises @ direct_premises


let set_euf _ = { TraceSequent.t_euf = true }

(** [euf_apply f_select judge sk fk] selects an atom of the judgement according
   to [f_selct] and then try to applly euf to it. If it fails, or f_select fails
   it calls [fk]*)
let euf_apply hypothesis_name (s : TraceSequent.t) sk fk =
  try
    let s, at =
      TraceSequent.select_message_hypothesis hypothesis_name s ~update:set_euf in
    sk (euf_apply_facts s at) fk
  with Euf.Bad_ssc -> fk Tactics.NoSSC
     | Not_found -> raise @@ Tactics.Tactic_hard_failure
         (Tactics.Failure "no hypothesis with the given name")

let () =
  T.register_general "euf"
    ~help:"Apply the euf axiom to the given hypothesis name.\
           \n Usage: euf H."
    (function
      | [Prover.Theory (Theory.Var h)] -> euf_apply h
      | _ -> raise @@ Tactics.Tactic_hard_failure
          (Tactics.Failure "improper arguments"))

(** [apply gp ths judge sk fk] applies the formula named [gp],
  * eliminating its universally quantified variables using [ths],
  * and eliminating implications (and negations) underneath. *)
let apply id (ths:Theory.term list) (s : TraceSequent.t) sk fk =
  (* Get formula to apply *)
  let f,system =
    try TraceSequent.get_hypothesis id s, TraceSequent.system_id s with
      | Not_found -> Prover.get_goal_formula id
  in
  if system <> TraceSequent.system_id s && system <> Term.None then
    raise @@ Tactics.Tactic_hard_failure Tactics.NoAssumpSystem;
  let uvars,f = match f with
    | ForAll (uvars,f) -> uvars,f
    | _ -> [],f
  in
  let subst = Theory.parse_subst (TraceSequent.get_env s) uvars ths in
  (* Formula with universal quantifications introduced *)
  let f = Term.subst subst f in
  (* Compute subgoals by introducing implications on the left. *)
  let rec aux subgoals = function
    | Term.Impl (h,c) ->
        let s' = TraceSequent.set_conclusion h s in
        aux (s'::subgoals) c
    | Term.Not h ->
        let s' = TraceSequent.set_conclusion h s in
        sk (List.rev (s'::subgoals)) fk
    | f ->
        TraceSequent.add_formula f s ::
        List.rev subgoals
        |> fun subgoals -> sk subgoals fk
  in
  aux [] f

let () =
  T.register_general "apply"
    ~help:"Apply an hypothesis with its universally quantified variables \
           \n instantiated with the arguments.\
           \n Usage: apply H to i1, i2, ..."
    (function
      | Prover.String_name id :: th_terms ->
          let th_terms =
            List.map
              (function
                 | Prover.Theory th -> th
                 | _ -> raise @@ Tactic_hard_failure
                     (Tactics.Failure "improper arguments"))
              th_terms
          in
          apply id th_terms
      | _ -> raise @@ Tactics.Tactic_hard_failure
          (Tactics.Failure "improper arguments"))

(** [tac_assert f j sk fk] generates two subgoals, one where [f] needs
  * to be proved, and the other where [f] is assumed. *)
let tac_assert f s sk fk =
  let s1 = TraceSequent.set_conclusion f s in
  let s2 = TraceSequent.add_formula f s in
  sk [s1 ;s2] fk

let () =
  T.register_formula "assert"
    ~help:"Add an assumption to the set of hypothesis, and produce the goal for\
           \n the proof of the assumption.\
           \n Usage: assert f."
    tac_assert

(** [collision_resistance judge sk fk] collects all equalities between hashes,
    and adds the equalities of the messages hashed with the same key. *)
let collision_resistance (s : TraceSequent.t) sk fk =
  (* We collect all hashes appearing inside the hypotheses, and which satisfy
     the syntactic side condition. *)
  let hashes = List.filter
      (fun t -> match t with
         | Fun ((hash, _), [m; Name (key,_)]) ->
             let system_id = TraceSequent.system_id s in
             Theory.is_hash hash && Euf.hash_key_ssc ~system_id hash key [m]
         | _ -> false)
      (TraceSequent.get_all_terms s)
  in
  if List.length hashes = 0 then
    fk (NoSSC)
  else
    begin
      let rec make_eq hash_list =
        match hash_list with
        | [] -> []
        | h1::q -> List.fold_left (fun acc h2 ->
            match h1, h2 with
            | Fun ((hash, _), [_; Name key1]), Fun ((hash2, _), [_; Name key2])
              when hash = hash2 && key1 = key2 -> (h1, h2) :: acc
            | _ -> acc
          ) [] q
      in
      let s,trs = TraceSequent.get_trs s in
      let hash_eqs = make_eq hashes
                     |> List.filter (fun eq -> Completion.check_equalities
                                        (trs) [eq])
      in
      let new_facts =
        List.fold_left (fun acc (h1,h2) ->
            match h1, h2 with
            | Fun ((hash, _), [m1; Name key1]),
              Fun ((hash2, _), [m2; Name key2])
              when hash = hash2 && key1 = key2 ->
              Term.Atom (`Message (`Eq, m1, m2)) :: acc
            | _ -> acc
          ) [] hash_eqs
      in
      let s =
        List.fold_left (fun s f ->
            TraceSequent.add_formula f s
          ) s new_facts
      in
      sk [s] fk
    end

let () = T.register "collision"
    ~help:"Collects all equalities between hashes, and affs the equalities of \
           \n the messages hashed with the same valid key.\
           \n Usage: collision."
    collision_resistance

(** Projecting a goal on a bi-system
  * to distinct goals for each projected system. *)

let project s sk fk =
  if TraceSequent.system_id s <> None then
    fk (Tactics.Failure "goal already deals with a single process")
  else
    let s1 = TraceSequent.set_system_id Left s in
    let s2 = TraceSequent.set_system_id Right s in
    let s1 = TraceSequent.pi Left s1 in
    let s2 = TraceSequent.pi Right s2 in
    sk [s1;s2] fk

let () =
  T.register "project"
    ~help:"Project a goal on a bi-system into goals on its projections."
    project
