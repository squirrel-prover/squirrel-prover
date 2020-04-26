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

let print (s : TraceSequent.t) sk fk =
  Printer.prt `Result "@.%a@." Action.pp_descrs (TraceSequent.system s);
   sk [s] fk

let () =
  T.register "print" ~help:"Shows the current system.\n Usage: print."
    print

(** Split a conjunction conclusion,
  * creating one subgoal per conjunct. *)
let goal_and_right (s : TraceSequent.t) sk fk =
  match TraceSequent.get_conclusion s with
  | And (lformula, rformula) ->
    sk [ TraceSequent.set_conclusion lformula s ;
         TraceSequent.set_conclusion rformula s ] fk
  | _ -> fk (Tactics.Failure "Cannot introduce a conjunction")

let () =
  T.register "split"
    ~help:"Split a conjunction conclusion, creating one subgoal per conjunct.\
           \n Usage: split."
    goal_and_right

(** Compute the goal resulting from the addition of a list of
  * formulas as hypotheses,
  * followed by the left intro of existentials and conjunctions. *)
let rec left_introductions s = function
  | (Term.And (f,g),prefix) :: l -> left_introductions s
                                      ((f,prefix)::(g,prefix)::l)
  | (Term.Exists (vars,f),prefix) :: l ->
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
        left_introductions (TraceSequent.set_env env s) ((f,prefix)::l)
  | (f, "") :: l -> left_introductions
                      (TraceSequent.add_formula f s) l
  | (f, prefix) :: l -> left_introductions
                          (TraceSequent.add_formula ~prefix f s) l
  | [] -> s

let left_intros hyp_name s sk fk =
  match TraceSequent.select_formula_hypothesis hyp_name s ~remove:true with
    | s,formula -> sk [left_introductions s [(formula,"")]] fk
    | exception Not_found -> fk (Tactics.Failure "no such hypothesis")

let () =
  T.register_general "introsleft"
    ~help:"Simplify conjunctions and existentials in an hypothesis.\
           \n Usage: introsleft H."
    (function
      | [Prover.Theory (Theory.Var h)] -> left_intros h
      | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))

let left_not_intro hyp_name s =
  let s,formula =
    TraceSequent.select_formula_hypothesis hyp_name s ~remove:true in
  let rec not_f = function
    | Exists (vs, f) -> ForAll(vs, not_f f)
    | ForAll (vs, f) -> Exists(vs, not_f f)
    | And (a, b) -> Or (not_f a, not_f b)
    | Or (a, b) -> And (not_f a, not_f b)
    | Impl (a, b) -> And(a, not_f b)
    | True -> False
    | False -> True
    | Not f -> f
    | Atom (#message_atom as a) ->
        Atom (Atom.not_message_atom a :> generic_atom)
    | Atom (#trace_atom as a) ->
        Atom (Atom.not_trace_atom a :> generic_atom)
    | m -> Not m
  in
  match formula with
  | Not f -> [TraceSequent.add_formula (not_f f) s]
  | _ -> Tactics.soft_failure (Tactics.Failure "cannot introduce negation")

let () =
  T.register_general "notleft"
    ~help:"Push a negation inside a formula.\
           \n Usage: notleft H."
    (function
      | [Prover.Theory (Theory.Var h)] ->
          fun s sk fk -> begin match left_not_intro h s with
            | subgoals -> sk subgoals fk
            | exception Tactics.Tactic_soft_failure e -> fk e
          end
      | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))


(** Case analysis on a timestamp *)
let timestamp_case ts s =
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
  let system = TraceSequent.system s in
  Action.iter_descrs system add_action ;
  [TraceSequent.add_formula !f s]

(** Case analysis on a disjunctive hypothesis *)
let hypothesis_case hypothesis_name (s : TraceSequent.t) =
  let s,f =
    TraceSequent.select_formula_hypothesis hypothesis_name s ~remove:true in
  let rec disjunction_to_list acc = function
    | Or (f,g) :: l -> disjunction_to_list acc (f::g::l)
    | f :: l -> disjunction_to_list (f::acc) l
    | [] -> acc
  in
  let formulas = disjunction_to_list [] [f] in
  if List.length formulas = 1 then
    Tactics.soft_failure
      (Tactics.Failure "can only be applied to a disjunction") ;
  List.rev_map (fun f -> TraceSequent.add_formula f s ) formulas

let case th s =
  (* if the conversion to a timestamp of the variable is successful, we perform
     a timestamp_case. If it fails, we try with hypothesis case. *)
    let tsubst = Theory.subst_of_env (TraceSequent.get_env s) in
    match Theory.convert tsubst th Sorts.Timestamp with
    | exception _ ->
      begin
        match th with
        | Theory.Var m ->
            begin try hypothesis_case m s with
              | Not_found -> Tactics.(soft_failure (Undefined m))
            end
        | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments")
      end
    | ts -> timestamp_case ts s

let () =
  T.register_general "case"
    ~help:"When T is a timestamp variable, introduce a disjunction \
           \n hypothesis expressing the various forms that it could take. \
           \n when T is a disjunction name, split the given disjunction on the \
           \n left, creating corresponding subgoals.\
           \n Usage: case T."
    (function
       | [Prover.Theory th] ->
          begin fun s sk fk -> match case th s with
            | subgoals -> sk subgoals fk
            | exception Tactics.Tactic_soft_failure e -> fk e
          end
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))

let depends t1 t2 s =
  let tsubst = Theory.subst_of_env (TraceSequent.get_env s) in
  let a1, a2 =
    try
      Theory.convert tsubst t1 Sorts.Timestamp,
      Theory.convert tsubst t2 Sorts.Timestamp
    with _ -> Tactics.soft_failure
                (Tactics.Failure "cannot convert arguments to timestamps")
  in
  match a1, a2 with
  | Term.Action( n1, is1), Term.Action (n2, is2) ->
    if Action.(depends (of_term n1 is1) (of_term n2 is2)) then
      let atom = (Atom (`Timestamp (`Lt,a1,a2))) in
      [TraceSequent.add_formula atom s]
    else
      Tactics.soft_failure
        (Tactics.NotDepends (Fmt.strf "%a" Term.pp a1,
                             Fmt.strf "%a" Term.pp a2))
  | _ -> Tactics.soft_failure (Tactics.Failure "arguments must be actions")

let () =
  T.register_general "depends"
    ~help:"If the second action given as argument depends on the first action,\
           \n add the corresponding timestamp inequality.\
           \n Usage: depends a1, a2."
    (function
       | [Prover.Theory t1; Prover.Theory t2] ->
           fun s sk fk -> begin match depends t1 t2 s with
             | subgoals -> sk subgoals fk
             | exception Tactics.Tactic_soft_failure e -> fk e
           end
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))

let false_left s =
  try
    let _ : formula =
      TraceSequent.find_formula_hypothesis
        (function False -> true | _ -> false) s
    in
    []
  with Not_found -> Tactics.(soft_failure @@ Failure "no False assumption")

let () =
  T.register_general "false_left"
    ~help:"Closes a goal when False is among its assumptions.\
           \n Usage: false_left."
    (function
       | [] ->
           fun s sk fk -> begin match false_left s with
             | subgoals -> sk subgoals fk
             | exception Tactics.Tactic_soft_failure e -> fk e
           end
       | _ -> Tactics.hard_failure (Tactics.Failure "no argument allowed"))

(** [goal_intro judge] perform introduces the topmost connective
  * of the conclusion formula, when this can be done in an invertible
  * and non-branching manner. *)
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
  | Exists ([],f) ->
    sk [TraceSequent.set_conclusion f s] fk
  | Impl(lhs,rhs)->
    let s' =
      TraceSequent.add_formula lhs (TraceSequent.set_conclusion rhs s) in
    sk [s'] fk
  | Not f ->
    sk [TraceSequent.set_conclusion False s |> TraceSequent.add_formula f] fk
  | True ->
    sk [] fk
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
    ~help:"Introduce topmost connective of conclusion formula, when \
           \n it can be done in an invertible, non-branching fashion.\
           \n Usage: intro."
    goal_intro

(** Quantifiers *)

(** [goal_exists_intro judge ths] introduces the existentially
    quantified variables in the conclusion of the judgment,
    using [ths] as existential witnesses. *)
let goal_exists_intro ths (s : TraceSequent.t) =
  match TraceSequent.get_conclusion s with
  | Exists (vs,f) when List.length ths = List.length vs ->
    begin try
      let nu = Theory.parse_subst (TraceSequent.get_env s) vs ths in
      let new_formula = Term.subst nu f in
      [TraceSequent.set_conclusion new_formula s]
    with Theory.(Conv (Undefined x)) ->
      Tactics.soft_failure (Tactics.Undefined x)
    end
  | _ ->
      Tactics.soft_failure (Tactics.Failure "cannot introduce exists")

let () =
  T.register_general "exists"
    ~help:"Introduce the existentially quantified variables in the conclusion \
           \n of the judgment, using the arguments as existential witnesses. \
           \n Usage: exists t_1, t_2."
    (fun l s sk fk ->
       let ths =
         List.map
           (function
              | Prover.Theory tm -> tm
              | _ -> Tactics.(hard_failure (Failure "improper arguments")))
           l
       in
         match goal_exists_intro ths s with
           | subgoals -> sk subgoals fk
           | exception Tactics.Tactic_soft_failure e -> fk e)

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
      | _ -> fk @@ Tactics.Failure "improper arguments"

let () =
  T.register_general "existsleft"
    ~help:"Introduce existential quantifier in hypothesis H.\
           \n Usage: existsleft H."
    (function
      | [Prover.Theory (Theory.Var h)] -> exists_left h
      | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))

let simpl_left s sk fk =
  match
    TraceSequent.remove_formula_hypothesis
      (function
         | False | And _ | Exists _ | Atom _ -> true
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
    | Atom _ as f, s' -> let s = TraceSequent.add_formula f s' in
        sk [s] fk
    | _ -> assert false
    | exception Not_found -> fk (Tactics.Failure "no such hypothesis")

let () =
  T.register "simpl_left"
    ~help:"Introduce all conjunctions, existentials and false hypotheses. \
           Reintroduces formulas that are now atoms."
    simpl_left

let () =
  let open Tactics in
  T.register_macro "intros"
    ~help:"Repeat intro.\n Usage: intros."
    (Repeat (Abstract ("intro",[]))) ;
  T.register_macro "anyintro"
    ~help:"Introduce topmost connective of goal formula, when invertible. \
           \n Usage: anyintro."
    (OrElse
       [ Abstract ("split",[]) ; Abstract ("intro",[]) ])

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
  else fk (Tactics.Failure "constraints satisfiable")

let expand (term : Theory.term) (s : TraceSequent.t) =
  let tsubst = Theory.subst_of_env (TraceSequent.get_env s) in
  let system = TraceSequent.system s in
  let succ subst = [TraceSequent.apply_subst subst s] in
  match Theory.convert tsubst term Sorts.Boolean with
    | Macro ((mn, sort, is),l,a) ->
      if Macros.is_defined mn a then
        succ [Term.ESubst (Macro ((mn, sort, is),l,a),
                           Macros.get_definition system sort mn is a)]
      else Tactics.soft_failure (Tactics.Failure "cannot expand this macro")
    | _ ->
      Tactics.soft_failure (Tactics.Failure "can only expand macros")
    | exception Theory.(Conv (Type_error _)) ->
      begin match Theory.convert tsubst term Sorts.Message with
        | Macro ((mn, sort, is),l,a) ->
          if Macros.is_defined mn a then
            succ [Term.ESubst (Macro ((mn, sort, is),l,a),
                             Macros.get_definition system sort mn is a)]
          else Tactics.soft_failure (Tactics.Failure "cannot expand this macro")
        | exception Theory.(Conv e) ->
          Tactics.soft_failure (Tactics.Cannot_convert e)
        | _ ->
          Tactics.soft_failure (Tactics.Failure "can only expand macros")
      end
    | exception Theory.(Conv e) ->
      Tactics.soft_failure (Cannot_convert e)

let () = T.register_general "expand"
    ~help:"Expand all occurences of the given macro inside the goal.\
           \n Usage: expand macro."
    (function
       | [Prover.Theory v1] ->
           fun s sk fk -> begin match expand v1 s with
             | subgoals -> sk subgoals fk
             | exception Tactics.Tactic_soft_failure e -> fk e
           end
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))


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

let fresh_param m1 m2 = match m1,m2 with
  | Name (n,is), _ -> (n,is,m2)
  | _, Name (n,is) -> (n,is,m1)
  | _ -> Tactics.soft_failure
          (Tactics.Failure "can only be applied on hypothesis of the form t=n or n=t")

(* Direct cases - names appearing in the term [t] *)
let mk_fresh_direct system n is t =
  (* iterate over [t] to search subterms of [t] equal to a name *)
  let names =
    let iter = new EquivTactics.get_names ~system false in
    iter#visit_message t ;
    iter#get_names
  in
  let names =
    List.fold_left
      (fun names (n',is') -> if n = n' then is'::names else names)
      [] names
  in
  (* build the disjunction expressing that there exists a name subterm of [t]
   * equal to the name ([n],[is]) *)
  List.fold_left
    Term.mk_or Term.False
    (List.sort_uniq Pervasives.compare
    (List.map
      (fun is' ->
         List.fold_left Term.mk_and Term.True
           (List.map2
              (fun i i' -> Term.Atom (`Index (`Eq, i, i')))
              is is'))
       names))

(* Indirect cases - names ([n],[is']) appearing in actions of the system *)
let mk_fresh_indirect system env n is t =
  let list_of_actions_from_term =
    let iter = new EquivTactics.get_actions ~system false in
    iter#visit_message t ;
    iter#get_actions
  and tbl_of_action_names = Hashtbl.create 10 in
  Action.(iter_descrs system
    (fun action_descr ->
      let iter = new EquivTactics.get_name_indices ~system true n in
      iter#visit_formula (snd action_descr.condition) ;
      iter#visit_message (snd action_descr.output) ;
      List.iter (fun (_,t) -> iter#visit_message t) action_descr.updates;
      (* we add only actions in which name [n] occurs *)
      let action_indices = iter#get_indices in
      if List.length action_indices > 0 then
        Hashtbl.add tbl_of_action_names action_descr action_indices));
  Hashtbl.fold
    (fun a indices_a formulas ->
      (* All indices occurring in [a] and [indices_a]. *)
      let indices =
        List.sort_uniq Pervasives.compare
          (List.concat (a.Action.indices::indices_a)) in
      let subst =
        List.map
          (fun i ->
             let i' = Vars.make_fresh_from_and_update env i in
             Term.ESubst (Term.Var i, Term.Var i'))
          indices
      in
      (* we apply [subst] to the action [a] and to [indices_a] *)
      let new_action =
        Action.to_term (Action.subst_action subst a.Action.action) in
      let indices_a = List.map (List.map (Term.subst_var subst)) indices_a in
      let timestamp_inequalities =
        List.fold_left Term.mk_or Term.False
          (List.sort_uniq Pervasives.compare
            (List.map
              (fun (action_from_term,strict) ->
                if strict
                (* [strict] is true if [action_from_term] refers to an input *)
                then Term.Atom (`Timestamp (`Lt, new_action, action_from_term))
                else Term.Atom (Term.mk_timestamp_leq new_action action_from_term))
              list_of_actions_from_term))
      in
      let index_equalities =
        List.fold_left Term.mk_or Term.False
          (List.map
             (fun is' ->
                List.fold_left Term.mk_and Term.True
                  (List.map2
                     (fun i i' -> Term.Atom (`Index (`Eq,i,i')))
                     is is'))
             indices_a)
      in
      let phi_a = Term.mk_and index_equalities timestamp_inequalities in
      Term.mk_or phi_a formulas)
    tbl_of_action_names
    Term.False

let fresh th s =
  match th with
  | Theory.Var m ->
    begin try
      let s,hyp =
        TraceSequent.select_message_hypothesis m s ~remove:false in
      begin match hyp with
      | `Message (`Eq,m1,m2) ->
        let (n,is,t) = fresh_param m1 m2 in
        let env = ref (TraceSequent.get_env s) in
        let system = TraceSequent.system s in
        let phi_direct = mk_fresh_direct system n is t in
        let phi_indirect = mk_fresh_indirect system env n is t in
        let new_hyp = Term.mk_or phi_direct phi_indirect in
        [TraceSequent.set_env !env (TraceSequent.add_formula new_hyp s)]
      | _ -> Tactics.soft_failure
              (Tactics.Failure "can only be applied on message hypothesis")
      end
    with
    | Not_found -> Tactics.(soft_failure (Undefined m))
    | EquivTactics.Var_found -> Tactics.soft_failure
                    (Tactics.Failure "can only be applied on ground terms")
    end
  | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments")

let () =
  T.register_general "fresh"
    ~help:"Given a message equality M of the form t=n, \
           add an hypothesis expressing that n is a subterm of t.\
           \n Usage: fresh M."
    (function
       | [Prover.Theory th] ->
          begin fun s sk fk -> match fresh th s with
            | subgoals -> sk subgoals fk
            | exception Tactics.Tactic_soft_failure e -> fk e
          end
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))

let substitute v1 v2 s =
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
        Tactics.soft_failure Tactics.NotEqualArguments
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
          Tactics.soft_failure Tactics.NotEqualArguments
      | exception _ ->
        match Theory.conv_index tsubst v1, Theory.conv_index tsubst v2 with
        | i1,i2 ->
          let s, models = TraceSequent.get_models s in
          if Constr.query models [(`Index (`Eq,i1,i2))] then
            [Term.ESubst (Term.Var i1,Term.Var i2)]
          else
            Tactics.soft_failure Tactics.NotEqualArguments
        | exception _ -> Tactics.(soft_failure (Failure "cannot convert"))
  in
  [TraceSequent.apply_subst subst s]

let () =
  T.register_general "substitute"
    ~help:"If the sequent implies that the arguments i1, i2 are equals,\
           \n replaces all occurences of i1 by i2 inside the sequent.\
           \n Usage: substitute i1, i2."
    (function
       | [Prover.Theory v1; Prover.Theory v2] ->
           fun s sk fk -> begin match substitute v1 v2 s with
             | subgoals -> sk subgoals fk
             | exception Tactics.Tactic_soft_failure e -> fk e
           end
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))


(** Expects a list of theory elements of the form cond@T :: formula :: l and
     output@T :: message :: l, and produces from it the corresponding
     substitution over Action.descrs. *)
let rec parse_substd tsubst s =
  match s with
  | [] -> []
  | [a] -> Tactics.(soft_failure (Failure "ill-typed substitution"))
  | (Prover.Theory mterm)::(Prover.Theory b)::q ->
    begin
      match Theory.convert tsubst mterm Sorts.Boolean,
            Theory.convert tsubst b Sorts.Boolean with
      |Term.Macro ((mn, sort, is),l,a), ncond ->
        begin
          match a with
          | Action (symb,indices) ->
            begin
              let action = Action.of_term symb indices in
              match Symbols.Macro.get_all mn with
              | Symbols.Cond, _ -> Action.Condition (ncond, action)
                                   :: parse_substd tsubst q
              | _ -> Tactics.(soft_failure (Failure "ill-typed substitution"))
            end
          | _ -> assert false
        end
      | exception _ ->
        begin
          match Theory.convert tsubst mterm Sorts.Message,
                Theory.convert tsubst b Sorts.Message with
          |Term.Macro ((mn, sort, is),l,a), nout ->
            begin
              match a with
              | Action (symb,indices) ->
                begin
                  let action = Action.of_term symb indices in
                  match Symbols.Macro.get_all mn with
                  | Symbols.Output, _ -> Action.Output (nout, action)
                                         :: parse_substd tsubst q
                  | _ -> Tactics.(soft_failure (Failure "ill-typed substitution"))
                end
              | _ -> assert false
              | exception Theory.Conv e -> Tactics.(soft_failure (Cannot_convert e))
            end
          | _ -> Tactics.(soft_failure (Failure "ill-typed substitution"))
        end
      | _ ->  Tactics.(soft_failure (Failure "ill-typed substitution"))
    end
  | _ ->  Tactics.(soft_failure (Failure "ill-typed substitution"))

(* Given a list of index names, and some remainder, instantiates the variables
   and produce the substitution. *)
let rec parse_indexes =
  function
  | [] -> ([],[],[])
  | Prover.Theory (Var i) :: q -> let id,vs,rem = parse_indexes q in
    let var =  snd (Vars.make_fresh Vars.empty_env Sorts.Index i) in
    Theory.ESubst (i, Term.Var var)::id
  , (Vars.EVar var)::vs, rem
  | a :: q -> let id,vs, rem = parse_indexes q in
    id,vs,a::rem

let equiv_goal_from_subst vs substd =
  let make_equiv a b =
    Term.And (Term.Impl (a, b), Term.Impl (b, a))
  in
  let rec conj_equiv =
    function
    | [] -> Term.True
    | Action.Condition (ncond, action) :: q ->
      let new_eq = make_equiv
                  (Term.Macro (Term.cond_macro,[],Action.to_term action))
                  ncond
      in
      if q <> [] then
        Term.And (new_eq, conj_equiv q)
      else
        new_eq
    | Action.Output (nout, action) :: q ->
      let new_eq = Term.Atom (`Message (`Eq,
                                        nout,
                                        (Term.Macro (Term.out_macro,[],Action.to_term action))
                                       ))
      in
      if q <> [] then
        Term.And (new_eq , conj_equiv q)
      else
        new_eq
  in
  Term.ForAll (vs, conj_equiv substd)

let system_subst new_system isubst vs subst s =
  let substdescr = parse_substd isubst subst in
  try
    Action.clone_system_subst (TraceSequent.system s) new_system substdescr;
    let new_goal =
      match TraceSequent.system s with
      | Pair _ | SimplePair _ ->
        TraceSequent.set_system (Action.SimplePair new_system) s
      | Single (Left _) ->
        TraceSequent.set_system (Action.Single (Left new_system)) s
      | Single (Right _) ->
        TraceSequent.set_system (Action.Single (Right new_system)) s
    in
    TraceSequent.set_conclusion (equiv_goal_from_subst vs substdescr) s :: [new_goal]
  with Action.SystemNotFresh ->
    Tactics.hard_failure (Tactics.Failure "System name already defined for another system.")

let () =
  T.register_general "systemsubstitute"
    ~help:"Modify the system of the current proof, so that the given \
           substitution over some cond@T or output@T has been applied, and \
           produces the subgoals asking that the substitution preserves equality \
           of distributions. \
           The system produced is named after the given named, and if a previous \
           system was already defined in the same way it does not recreate it.
           \n Usage: systemsubstitute new_sytem_name,i1,...,ik,\
           cond@T, newcond, output@T, newoutput, ... ."
    (function
      | Prover.Theory (Var system_name) :: q  ->
        let subst_index, vs, subst_descr = parse_indexes q in
        fun s sk fk -> begin
            match system_subst system_name subst_index vs subst_descr s with
             | subgoals -> sk subgoals fk
             | exception Tactics.Tactic_soft_failure e -> fk e
           end
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))


let exec a s =
  let tsubst = Theory.subst_of_env (TraceSequent.get_env s) in
  let a =
    try
      Theory.convert tsubst a Sorts.Timestamp
    with
      | Theory.Conv e -> Tactics.(soft_failure (Cannot_convert e))
  in
  let var = snd Vars.(make_fresh empty_env Sorts.Timestamp "t") in
  let formula =
    ForAll (
      [Vars.EVar (var)],
      Impl(Atom (Term.mk_timestamp_leq (Var var) a),
           Macro(Term.exec_macro,[],Var var)
          )
    )
  in
  [TraceSequent.add_formula formula s]

let () =
  T.register_general "executable"
    ~help:"Assert that exec@_ implies exec@_ for all \
           previous timestamps.\
           \n Usage: executable t."
    (function
       | [Prover.Theory v] ->
           fun s sk fk -> begin match exec v s with
             | subgoals -> sk subgoals fk
             | exception Tactics.Tactic_soft_failure e -> fk e
           end
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))


(** EUF Axioms *)

let euf_param (`Message at : message_atom) = match at with
  | (`Eq, Fun ((checksign, _),
               [s;
               Fun ((pk,_), [Name key])
               ]), m)
  | (`Eq, m, Fun ((checksign, _),
               [s;
               Fun ((pk,_), [Name key])
               ])) ->
      begin match Theory.check_signature checksign pk with
      | None ->
          Tactics.(soft_failure @@
                   Failure "the message does not correspond \
                            to a signature check with the associated pk")
      | Some sign -> (sign, key, m, s, Some pk)
      end

  | (`Eq, Fun ((hash, _), [m; Name key]), s) when Theory.is_hash hash ->
    (hash, key, m, s, None)
  | (`Eq, s, Fun ((hash, _), [m; Name key])) when Theory.is_hash hash ->
    (hash, key, m, s, None)

  | _ -> Tactics.soft_failure
           (Tactics.Failure
              "euf can only be applied to hypothesis of the form h(t,k)=m
              or m=h(t,k) with h a hash function symbol")

let euf_apply_schema sequent (_, (_, key_is), m, s, _) case =
  let open Euf in

  (* Equality between hashed messages *)
  let new_f = Term.Atom (`Message (`Eq, case.message, m)) in

  (* Equalities between key indices *)
  let eq_indices =
    List.fold_left2
      (fun cnstr i i' ->
         Term.mk_and cnstr (Term.Atom (`Index (`Eq, i, i'))))
      Term.True
      key_is case.key_indices
  in

  (* Now, we need to add the timestamp constraints. *)
  (* The action name and the action timestamp variable are equal. *)
  let action_descr_ts = Action.to_term case.action_descr.Action.action in
  (* The action occured before the test H(m,k) = s. *)
  let le_cnstr =
    List.map
      (function ts ->
        Term.Atom (Term.mk_timestamp_leq action_descr_ts ts))
      (snd (TraceSequent.maximal_elems sequent (precise_ts s @ precise_ts m)))
  in
  let le_cnstr = List.fold_left Term.mk_or Term.False le_cnstr in

  let sequent = TraceSequent.set_env case.env sequent in
  let sequent =
    if eq_indices = Term.True then sequent else
      TraceSequent.add_formula eq_indices sequent
  in
    TraceSequent.add_formula new_f
      (TraceSequent.add_formula le_cnstr sequent)

let euf_apply_direct s (_, (_, key_is), m, _, _) Euf.{d_key_indices;d_message} =
  (* The components of the direct case may feature variables that are
   * not in the current environment: this happens when the case is extracted
   * from under a binder, e.g. a Seq or ForAll construct. We need to add
   * such variables to the environment. *)
  let init_env = TraceSequent.get_env s in
  let subst,env =
    List.fold_left
      (fun (subst,env) (Vars.EVar v) ->
         if Vars.mem init_env (Vars.name v) then subst,env else
         let env,v' = Vars.make_fresh_from env v in
         let subst = Term.(ESubst (Var v, Var v')) :: subst in
         subst,env)
      ([],init_env)
      (List.sort_uniq Pervasives.compare
         (List.map (fun i -> Vars.EVar i) d_key_indices @
          Term.get_vars d_message))
  in
  let s = TraceSequent.set_env env s in
  let d_message = Term.subst subst d_message in

  (* Equality between hashed messages. *)
  let eq_hashes = Term.Atom (`Message (`Eq, d_message, m)) in

  (* Equality between key indices. *)
  let eq_indices =
    List.fold_left2
      (fun cnstr i i' ->
         let i' = Term.subst_var subst i' in
         Term.mk_and cnstr (Term.Atom (`Index (`Eq, i, i'))))
      Term.True
      key_is d_key_indices
  in

  TraceSequent.add_formula eq_hashes s
  |> TraceSequent.add_formula eq_indices

let euf_apply_facts s at =
  let p = euf_param at in
  let env = TraceSequent.get_env s in
  let (hash_fn, (key_n, key_is), mess, sign, pk) = p in
  let system = TraceSequent.system s in
  let rule = Euf.mk_rule ~pk ~system ~env ~mess ~sign ~hash_fn ~key_n ~key_is in
  let schemata_premises =
    List.map (fun case -> euf_apply_schema s p case) rule.Euf.case_schemata
  and direct_premises =
    List.map (fun case -> euf_apply_direct s p case) rule.Euf.cases_direct
  in
  schemata_premises @ direct_premises

let set_euf _ = { TraceSequent.t_euf = true }

(** Tag EUFCMA - for composition results *)
let euf_apply hypothesis_name (s : TraceSequent.t) sk fk =
  let s, at =
    try
      TraceSequent.select_message_hypothesis hypothesis_name s ~update:set_euf
    with Not_found ->
      Tactics.hard_failure
        (Tactics.Failure "no hypothesis with the given name")
  in
  let tag_s =
    let (h,key,m,_,_) = euf_param at in
    let f =
      Prover.get_hash_tag_formula (Symbols.to_string h)
    in
    (* if the hash is not tagged, the formula is False, and we don't create
       another goal. *)
    if f = Term.False  then
      []
    else
      (* else, we create a goal where m,sk satisfy the axiom *)
      let (Vars.EVar uvarm),(Vars.EVar uvarkey),f = match f with
        | ForAll ([uvarm;uvarkey],f) -> uvarm,uvarkey,f
        | _ -> assert false
      in
      match Vars.sort uvarm,Vars.sort uvarkey with
      | Sorts.(Message, Message) -> let f = Term.subst [
          ESubst (Term.Var uvarm,m);
          ESubst (Term.Var uvarkey,Term.Name key);] f in
        [TraceSequent.add_formula f s]
      | _ -> assert false
  in
    (* we create the honnest sources using the classical eufcma tactic *)
    try
      let honest_s = euf_apply_facts s at in
      sk (tag_s @ honest_s) fk
    with Euf.Bad_ssc ->  fk Tactics.Bad_SSC

let () =
  T.register_general "euf"
    ~help:"Apply the euf axiom to the given hypothesis name. If the hash has\
           \n been declared with a tag formula, applies the tagged version.\
           \n given tag. Tagged eufcma, with a tag T, says that, under the\
           \n syntactic side condition, a hashed message either satisfies\
           \n the tag T, or was honnestly produced. \
           \n The tag T must refer to a previously defined axiom f(mess,sk), of\
           \n the form forall (m:message,sk:message).
           \n Usage: tageuf H t."
    (function
      | [Prover.Theory (Theory.Var h)] -> euf_apply h
      | _ -> Tactics.(hard_failure (Failure "improper arguments")))

(** [apply gp ths judge sk fk] applies the formula named [gp],
  * eliminating its universally quantified variables using [ths],
  * and eliminating implications (and negations) underneath. *)
let apply id (ths:Theory.term list) (s : TraceSequent.t) sk fk =
  (* Get formula to apply *)
  let f,system =
    try TraceSequent.get_hypothesis id s, TraceSequent.system s with
      | Not_found -> Prover.get_goal_formula id
  in
  begin
    match TraceSequent.system s, system with
    | s1, s2  when s1 = s2 -> ()
    | Single(Left s1), Action.SimplePair s2  when s1 = s2 -> ()
    | Single(Right s1), Action.SimplePair s2  when s1 = s2 -> ()
    | _ -> Tactics.hard_failure Tactics.NoAssumpSystem
  end ;
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
                 | _ -> Tactics.hard_failure
                          (Tactics.Failure "improper arguments"))
              th_terms
          in
          apply id th_terms
      | _ -> Tactics.hard_failure
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
           let system = TraceSequent.system s in
             Theory.is_hash hash
              && Euf.check_hash_key_ssc ~messages:[m] ~pk:None ~system hash key
         | _ -> false)
      (TraceSequent.get_all_terms s)
  in
  if List.length hashes = 0 then
    fk Tactics.NoSSC
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

(** Automated goal simplification *)

let () =
  let open Tactics in
  (* Simplify goal. We will never backtrack on these applications. *)
  let simplify =
    andthen_list [
      (* Try assumption first to avoid loosing the possibility
       * of doing it after introductions. *)
      try_tac assumption ;
      repeat goal_intro ;
      repeat simpl_left ;
      eq_names ;
      eq_trace
    ]
  in
  (* Attempt to close a goal. *)
  let conclude =
    orelse_list [congruence;constraints;assumption]
  in
  let (>>) = andthen ~cut:true in
  (* If [close] then automatically prove the goal,
   * otherwise it may also be reduced to a single subgoal. *)
  let rec simpl close : TraceSequent.t tac =
    simplify >> try_tac conclude >>
      fun g sk fk ->
        (* If we still have a goal, we can try to split a conjunction
         * and prove the remaining subgoals, or return this goal,
         * but we must respect [close]. *)
        let fk =
          if close then
            fun _ -> fk (Failure "cannot automatically prove goal")
          else
            fun _ -> sk [g] fk
        in
        goal_and_right g
          (fun l _ -> match l with
             | [g1;g2] ->
                 simpl close g1
                   (fun l' _ ->
                      if l'=[] then
                        simpl close g2 sk fk
                      else
                        simpl true g2
                          (fun l'' fk -> assert (l'' = []) ; sk l' fk)
                          fk)
                   fk
             | _ -> assert false)
          fk
  in
  T.register "simpl" (simpl false) ;
  T.register "auto" (simpl true)

(** Projecting a goal on a bi-system
  * to distinct goals for each projected system. *)

let project s sk fk =
  let system = TraceSequent.system s in
  match system with
  | Single _ -> fk (Tactics.Failure "goal already deals with a single process")
  | _ ->
    let s1 = TraceSequent.set_system Action.(project_system Term.Left system) s in
    let s2 = TraceSequent.set_system Action.(project_system Term.Right system) s in
    let s1 = TraceSequent.pi Left s1 in
    let s2 = TraceSequent.pi Right s2 in
    sk [s1;s2] fk

let () =
  T.register "project"
    ~help:"Project a goal on a bi-system into goals on its projections."
    project
