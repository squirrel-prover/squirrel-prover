open Tactics
open Atom
open Formula
open Term

type tac = Sequent.t Tactics.tac

module T = Prover.Prover_tactics

(** Propositional connectives *)

let goal_or_right_1 (s : Sequent.t) sk fk =
  match Sequent.get_conclusion s with
  | (Or (lformula, _)) -> sk [Sequent.set_conclusion (lformula) s] fk
  | _ -> fk (Tactics.Failure "Cannot introduce a disjunction")

let goal_or_right_2 (s : Sequent.t) sk fk =
  match Sequent.get_conclusion s with
  | (Or (_, rformula)) -> sk [Sequent.set_conclusion (rformula) s] fk
  | _ -> fk (Tactics.Failure "Cannot introduce a disjunction")

let () =
  T.register "left"
    ~help:"Reduce a goal with a disjunction conclusion into the goal \
           where the conclusion has been replaced with the first disjunct."
    goal_or_right_1 ;
  T.register "right"
    ~help:"Reduce a goal with a disjunction conclusion into the goal \
           where the conclusion has been replace with the second disjunct."
    goal_or_right_2

let goal_true_intro (s : Sequent.t) sk fk =
  match Sequent.get_conclusion s with
  | True -> sk [] fk
  | _ -> fk (Tactics.Failure "Cannot introduce true")

let () =
  T.register "true" ~help:"Concludes if the goal is true." goal_true_intro

let goal_and_right (s : Sequent.t) sk fk =
  match Sequent.get_conclusion s with
  | And (lformula, rformula) ->
    sk [ Sequent.set_conclusion (lformula) s;
         Sequent.set_conclusion (rformula) s ] fk
  | _ -> fk (Tactics.Failure "Cannot introduce a conjonction")

let () =
  T.register "split"
    ~help:"Split a conjunction conclusion, creating one subgoal per conjunct."
    goal_and_right

(** Compute the goal resulting from the addition of a list of
  * formulas as hypotheses,
  * followed by the left intro of existentials and conjunctions. *)
let rec left_introductions s = function
  | Formula.And (f,g) :: l -> left_introductions s (f::g::l)
  | Formula.Exists (vars,f) :: l ->
      let env = Sequent.get_env s in
      let subst,env =
        List.fold_left
          (fun (subst,env) (Vars.EVar v) ->
             let env,v' =
               Vars.make_fresh env (Vars.sort v) (Vars.name v)
             in
             let item =
               let open Term in
               match Vars.sort v with
                 | Sorts.Index -> ESubst (Var v,Var v')
                 | Sorts.Timestamp -> ESubst (Var v, Var v')
                 | Sorts.Message -> ESubst (Var v, Var v')
                 | Sorts.Boolean -> ESubst (Var v, Var v')
             in
               item::subst, env)
          ([],env)
          vars
      in
      let f = Formula.subst_formula subst f in
        left_introductions (Sequent.set_env env s) (f::l)
  | f :: l -> left_introductions (Sequent.add_formula f s) l
  | [] -> s

let timestamp_case ts s sk fk =
  let f = ref (Atom (`Timestamp (`Eq,ts,Term.Init))) in
  let add_action a =
    let indices =
      let env = ref @@ Sequent.get_env s in
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
      let at = Atom (`Timestamp (`Eq,ts,name)) in
      let at = subst_formula subst at in
      if indices = [] then at else
        Exists (List.map (fun x -> Vars.EVar x) indices,at)
    in
    f := Formula.Or (case,!f)
  in
  Action.iter_descrs add_action ;
  sk [Sequent.add_formula !f s] fk

let hypothesis_case hypothesis_name (s : Sequent.t) sk fk =
  let s,f = Sequent.select_formula_hypothesis hypothesis_name s ~remove:true in
  let rec disjunction_to_list acc = function
    | Or (f,g) :: l -> disjunction_to_list acc (f::g::l)
    | f :: l -> disjunction_to_list (f::acc) l
    | [] -> acc
  in
  let formulas = disjunction_to_list [] [f] in
  if List.length formulas = 1 then
    raise @@
    Tactics.Tactic_Hard_Failure "Can only be applied to a disjunction." ;
  sk (List.rev_map (fun f -> Sequent.add_formula f s ) formulas) fk

let case th s sk fk =
  (* if the conversion to a timestamp of the variable is successful, we perform
     a timestamp_case. If it fails, we try with hypothesis case. *)
    let tsubst = Theory.subst_of_env (Sequent.get_env s) in
    match Theory.convert_ts tsubst th with
    | exception _ ->
      begin
        match th with
        | Theory.Var m -> hypothesis_case m s sk fk
        | _ -> raise @@ Tactics.Tactic_Hard_Failure "improper arguments"
      end
    | ts -> timestamp_case ts s sk fk

let () =
  T.register_general "case"
    ~help:"case T -> when T is a timestamp variable, \
           introduce a disjunction hypothesis expressing the various \
           forms that it could take. \
           when T is a disjunction name, split the given disjunction \
           on the left, creating corresponding subgoals."
    (function
       | [Prover.Theory th] -> case th
       | _ -> raise @@ Tactics.Tactic_Hard_Failure "improper arguments")


(** Introduce disjunction and implication (with conjunction on its left).
  * TODO this is a bit arbitrary, and it will be surprising for
  * users that "intro" does not introduce universal quantifiers. *)
let goal_intro (s : Sequent.t) sk fk =
  match Sequent.get_conclusion s with
  | ForAll (vs,f) ->
    let env = ref (Sequent.get_env s) in
    let subst =
      List.map
        (fun (Vars.EVar x) ->
           Term.ESubst (Term.Var x,
                        Term.Var (Vars.make_fresh_from_and_update env x)))
        vs
    in
    let new_formula = subst_formula subst f in
    let new_judge = Sequent.set_conclusion new_formula s
                    |> Sequent.set_env (!env)
    in
    sk [new_judge] fk
  | Impl(lhs,rhs)->
    let s' = left_introductions (Sequent.set_conclusion rhs s) [lhs] in
    sk [s'] fk
  | Not f ->
    sk [Sequent.set_conclusion False s |> Sequent.add_formula f] fk
  | Atom (`Message (`Neq,u,v)) ->
    let h = `Message (`Eq,u,v) in
    let s' = Sequent.set_conclusion False s |> Sequent.add_formula (Atom h) in
    sk [s'] fk
  | _ ->
      fk (Tactics.Failure
            "Can only introduce implication, universal quantifications \
             and disequality conclusions.")

let () =
  T.register "intro"
    ~help:"Performs one introduction, either of a forall \
           quantifier or an implication."
    goal_intro

(** Quantifiers *)

let goal_exists_intro ths (s : Sequent.t) sk fk =
  match Sequent.get_conclusion s with
  | Exists (vs,f) when List.length ths = List.length vs ->
    let nu = Theory.parse_subst (Sequent.get_env s) vs ths in
    let new_formula = subst_formula nu f in
    sk [Sequent.set_conclusion new_formula s] fk
  | _ -> fk (Tactics.Failure "Cannot introduce an exists")

let () =
  T.register_general "exists"
    ~help:"Introduce the existentially \
           quantified variables in the conclusion of the judgment, \
           using the arguments as existential witnesses. \
           Usage : exists t_1, t_2."
    (fun l ->
       let ths =
         List.map
           (function
              | Prover.Theory tm -> tm
              | _ -> raise @@ Tactic_Hard_Failure "Improper arguments")
           l
       in
       goal_exists_intro ths)

(* TODO exists_left without hypothesis name, select any existential
 * formula on the left *)
let exists_left hyp_name s sk fk =
  let s,f = Sequent.select_formula_hypothesis hyp_name s ~remove:true in
    match f with
      | Exists (vs,f) ->
          let env = ref @@ Sequent.get_env s in
          let subst =
            List.map
              (fun (Vars.EVar v) ->
                 Term.ESubst  (Term.Var v,
                               Term.Var (Vars.make_fresh_from_and_update env v))
              )
              vs
          in
          let f = subst_formula subst f in
          let s = Sequent.add_formula f (Sequent.set_env !env s) in
            sk [s] fk
      | _ -> fk @@ Tactics.Failure "Improper arguments"

let () =
  T.register_general "existsleft"
    ~help:"exists-left H -> introduce existential quantifier in hypothesis H"
    (function
      | [Prover.Theory (Theory.Var h)] -> exists_left h
      | _ -> raise @@ Tactics.Tactic_Hard_Failure "improper arguments")

let () =
  let open Prover.AST in
  let non_branching_intro =
    [ Abstract ("intro",[]) ;
      Abstract ("exists",[]) ;
      Abstract ("true",[]) ]
  in
  T.register_macro "intros"
    ~help:"Repeat intro."
    (Repeat (OrElse non_branching_intro)) ;
  T.register_macro "anyintro"
    ~help:"Try any possible introduction."
    (OrElse
       (Abstract ("split",[]) :: non_branching_intro))

(** Induction *)

let induction s sk fk =
  match Sequent.get_conclusion s with
  | ForAll ((Vars.EVar v)::vs,f) ->
    (match Vars.sort v with
       Sorts.Timestamp ->
       (
         (* We need two fresh variables in env,
          * but one will not be kept in the final environment. *)
         let env,v' = Vars.make_fresh_from (Sequent.get_env s) v in
         let _,v'' = Vars.make_fresh_from env v in
         (* Introduce v as v'. *)
         let f' = Formula.subst_formula [Term.ESubst (Term.Var v,Term.Var v')]
             (ForAll (vs,f))
         in
         (* Use v'' to form induction hypothesis. *)
         let ih =
           ForAll ((Vars.EVar v'')::vs,
                   Impl
                     (Atom (`Timestamp (`Lt,Term.Var v'',Term.Var v)
                            :> generic_atom),
                      Formula.subst_formula
                        [Term.ESubst (Term.Var v,Term.Var v'')] f))
         in
         let s =
           s
           |> Sequent.set_env env
           |> Sequent.set_conclusion f'
           |> Sequent.add_formula ~prefix:"IH" ih
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
    ~help:"Apply the induction scheme to the given formula."
    induction

(** Reasoning over constraints and messages *)

let constraints (s : Sequent.t) sk fk =
  if Sequent.constraints_valid s then
    sk [] fk
  else fk (Tactics.Failure "Constraints satisfiable")

let congruence (s : Sequent.t) sk fk =
  if Sequent.message_atoms_valid s then
    sk [] fk
  else fk (Tactics.Failure "Equations satisfiable")

let () = T.register "congruence"
    ~help:"Tries to derive false from the messages equalities."
    congruence

let () = T.register "constraints"
    ~help:"Tries to derive false from the trace formulas."
    constraints

let assumption (s : Sequent.t) sk fk =
  if Sequent.is_hypothesis (Sequent.get_conclusion s) s then
      sk [] fk
  else
    fk (Tactics.Failure "Conclusion is not an hypothesis")

let () = T.register "assumption"
    ~help:"Search for the conclusion inside the Hypothesis."
    assumption

(** Utils *)

let mk_or_cnstr l = match l with
  | [] -> Bformula.False
  | [a] -> a
  | a :: l' ->
    let rec mk_c acc = function
      | [] -> acc
      | x :: l -> mk_c (Bformula.Or (x,acc)) l in
    mk_c a l'

let mk_and_cnstr l = match l with
  | [] -> Bformula.True
  | [a] -> a
  | a :: l' ->
    let rec mk_c acc = function
      | [] -> acc
      | x :: l -> mk_c (Bformula.And (x,acc)) l in
    mk_c a l'

(** Eq-Indep Axioms *)

(* We include here rules that are specialization of the Eq-Indep axiom. *)

let eq_names (s : Sequent.t) sk fk =
  let s,trs = Sequent.get_trs s in
  let terms = Sequent.get_all_terms s in
  (* we start by collecting equalities between names implied by the indep axiom.
  *)
  let new_eqs = Completion.name_indep_cnstrs trs terms in
  let s =
    List.fold_left (fun _ c ->
        Sequent.add_formula c s
      ) s new_eqs
  in
  (* we now collect equalities between timestamp implied by equalities between
     names. *)
  let s,trs = Sequent.get_trs s in
  let cnstrs = Completion.name_index_cnstrs trs
      (Sequent.get_all_terms s)
  in
  let s =
    List.fold_left (fun _ c ->
        Sequent.add_trace_formula c s
      ) s cnstrs
  in
  sk [s] fk

let () = T.register "eqnames"
    ~help:" Add index constraints resulting from names equalities, modulo the \
known equalities."
    eq_names

let eq_timestamps (s : Sequent.t) sk fk =
  let ts_classes = Sequent.get_ts_equalities s
                   |> List.map (List.sort_uniq Pervasives.compare)
  in
  let subst =
    let rec asubst e = function
        [] -> []
      | p::q -> Term.ESubst (p,e) :: (asubst e q)
    in
    List.map (function [] -> [] | p::q -> asubst p q) ts_classes
    |> List.flatten
  in
  let terms = Sequent.get_all_terms s in
  let facts =
    List.fold_left
      (fun acc t ->
         let normt : Term.message = Term.subst subst t in
         if normt = t then
           acc
         else
           Formula.Atom (`Message (`Eq, t, normt)) ::acc)
      [] terms
  in
  let s =
    List.fold_left
      (fun s c ->
         Sequent.add_formula c s)
      s facts
  in
  sk [s] fk

let () = T.register "eqtimestamps"
    ~help:"Add terms constraints resulting from timestamp equalities."
    eq_timestamps

let substitute (v1) (v2) (s : Sequent.t) sk fk=
  let tsubst = Theory.subst_of_env (Sequent.get_env s) in
  let subst =
    match Theory.convert_ts tsubst v1, Theory.convert_ts tsubst v2 with
    | ts1,ts2 ->
      let models = Sequent.get_models s in
      if Constr.query models [(`Timestamp (`Eq,ts1,ts2))] then
        [Term.ESubst (ts1,ts2)]
      else
        raise @@ Tactic_Hard_Failure "Arguments not equals."
    | exception _ ->
      match Theory.convert_glob tsubst v1, Theory.convert_glob tsubst v2 with
      | m1,m2 ->
        let _,trs = Sequent.get_trs s in
        if Completion.check_equalities trs [(m1,m2)] then
          [Term.ESubst (m1,m2)]
      else
        raise @@ Tactic_Hard_Failure "Arguments not equals."
      | exception _ ->
        match Theory.conv_index tsubst v1, Theory.conv_index tsubst v2 with
        | i1,i2 ->
          let models = Sequent.get_models s in
          if Constr.query models [(`Index (`Eq,i1,i2))] then
            [Term.ESubst (Term.Var i1,Term.Var i2)]
          else
            raise @@ Tactic_Hard_Failure "Arguments not equals."
      | exception _ ->  raise @@ Tactic_Hard_Failure "Improper arguments."
  in
  sk [Sequent.apply_subst subst s] fk

let () =
  T.register_general "substitute"
    ~help:"substitute to i1, i2 -> if i1=i2 is implied by the sequent, replaces \
           all occurents of i1 by i2 inside the sequent."
    (function
       | [Prover.Theory v1; Prover.Theory v2] -> substitute v1 v2
       | _ -> raise @@ Tactics.Tactic_Hard_Failure "improper arguments")


(** EUF Axioms *)

let euf_param (`Message at : term_atom) = match at with
  | (`Eq, Fun ((hash, _), [m; Name key]), s)
  | (`Eq, s, Fun ((hash, _), [m; Name key]))->
    if Theory.is_hash hash then
      (hash, key, m, s)
    else raise @@ Tactic_Hard_Failure
        "The function symbol is not a hash function."
  | _ -> raise @@ Tactic_Hard_Failure
        "Euf can only be applied to hypothesis of the form h(t,k)=m."

let euf_apply_schema sequent (_, (_, _), m, s) case =
  let open Euf in
  (* We create the term equality *)
  let new_f = Formula.Atom (`Message (`Eq, case.message, m)) in
  (* Now, we need to add the timestamp constraints. *)
  (* The action name and the action timestamp variable are equal. *)
  let action_descr_ts = Action.to_term case.action_descr.Action.action in
  (* The action occured before the test H(m,k) = s. *)
  let le_cnstr =
    List.map
      (function
         | Pred ts ->
             Bformula.Atom (`Timestamp (`Lt, action_descr_ts, ts))
         | ts ->
             Bformula.Atom (`Timestamp (`Leq, action_descr_ts, ts)))
      (Sequent.maximal_elems sequent (precise_ts s @ precise_ts m))
    |> mk_or_cnstr
  in
  (new_f, le_cnstr, case.env)

let euf_apply_direct _ (_, (_, key_is), m, _) dcase =
  let open Euf in
  (* We create the term equality *)
  let eq = Formula.Atom (`Message (`Eq, dcase.d_message, m)) in
  (* Now, we need to add the timestamp constraint between [key_is] and
     [dcase.d_key_indices]. *)
  let eq_cnstr =
    List.map2
      (fun i i' -> Bformula.Atom (`Index (`Eq, i, i')))
      key_is dcase.d_key_indices
    |> mk_and_cnstr
  in
  (eq, eq_cnstr)

(* TODO : make error reporting for euf more informative *)
let euf_apply_facts s at =
  let p = euf_param at in
  let env = Sequent.get_env s in
  let (hash_fn, (key_n, key_is), mess, sign) = p in
  let rule = Euf.mk_rule ~env ~mess ~sign ~hash_fn ~key_n ~key_is in
  let schemata_premises =
    List.map (fun case ->
        let new_f, new_cnstr, new_env = euf_apply_schema s p case in
        Sequent.add_formula new_f s
        |> Sequent.add_trace_formula new_cnstr
        |> Sequent.set_env new_env
      ) rule.Euf.case_schemata
  and direct_premises =
    List.map (fun case ->
        let new_f, new_cnstr = euf_apply_direct s p case in
        Sequent.add_formula new_f s
        |> Sequent.add_trace_formula new_cnstr
      ) rule.Euf.cases_direct
  in
  schemata_premises @ direct_premises


let set_euf _ = { Sequent.t_euf = true }

let euf_apply hypothesis_name (s : Sequent.t) sk fk =
  let s, at =
    Sequent.select_message_hypothesis hypothesis_name s ~update:set_euf in
  (* TODO: need to handle failure somewhere. *)
  try
    sk (euf_apply_facts s at) fk
  with Euf.Bad_ssc -> fk (Tactics.Failure "The key of the hash does not \
satisfy the syntactic side condition")

let () =
  T.register_general "euf"
    ~help:"euf H -> applies the euf axiom to the given hypothesis name."
    (function
      | [Prover.Theory (Theory.Var h)] -> euf_apply h
      | _ -> raise @@ Tactics.Tactic_Hard_Failure "improper arguments")

let apply id (ths:Theory.term list) (s : Sequent.t) sk fk =
  (* Get formula to apply *)
  let f =
    try Sequent.get_hypothesis id s with
      | Not_found -> Prover.get_goal_formula id
  in
  let uvars,f = match f with
    | ForAll (uvars,f) -> uvars,f
    | _ -> [],f
  in
  let subst = Theory.parse_subst (Sequent.get_env s) uvars ths in
  (* Formula with universal quantifications introduced *)
  let f = subst_formula subst f in
  (* Compute subgoals by introducing implications on the left. *)
  let rec aux subgoals = function
    | Formula.Impl (h,c) ->
        let s' = Sequent.set_conclusion h s in
        aux (s'::subgoals) c
    | Formula.Not h ->
        let s' = Sequent.set_conclusion h s in
        sk (List.rev (s'::subgoals)) fk
    | f ->
        left_introductions s [f] ::
        List.rev subgoals
        |> fun subgoals -> sk subgoals fk
  in
  aux [] f

let () =
  T.register_general "apply"
    ~help:" apply gname to t_1,t_2 -> applies the axiom gname with its \
universally quantified variables instantied with t1,..."
    (function
      | Prover.String_name id :: th_terms ->
          let th_terms =
            List.map
              (function
                 | Prover.Theory th -> th
                 | _ -> raise @@ Tactic_Hard_Failure "improper arguments")
              th_terms
          in
          apply id th_terms
      | _ -> raise @@ Tactics.Tactic_Hard_Failure "improper arguments")

let tac_assert f s sk fk =
  let s1 = Sequent.set_conclusion f s in
  let s2 = Sequent.add_formula f s in
  sk [s1 ;s2] fk

let () =
  T.register_formula "assert"
    ~help:"Add an assumption to the set of hypothesis."
    tac_assert

let collision_resistance (s : Sequent.t) sk fk =
  (* We collect all hashes appearing inside the hypotheses, and which satisfy
     the syntactic side condition. *)
  let hashes = List.filter
      (fun t -> match t with
         | Fun ((hash, _), [m; Name (key,_)]) ->
           (Theory.is_hash hash) && (Euf.hash_key_ssc hash key [m])
         | _ -> false)
      (Sequent.get_all_terms s)
  in
  if List.length hashes = 0 then
    fk (Failure "no equality between hashes where the keys satisfiy the \
 syntactic condition has been found")
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
      let s,trs = Sequent.get_trs s in
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
              Formula.Atom (`Message (`Eq, m1, m2)) :: acc
            | _ -> acc
          ) [] hash_eqs
      in
      let s =
        List.fold_left (fun s f ->
            Sequent.add_formula f s
          ) s new_facts
      in
      sk [s] fk
    end

let () = T.register "collision"
    ~help:"Collects all equalities between hashes, and affs the equalities of \
the messages hashed with the same valid key."
    collision_resistance
