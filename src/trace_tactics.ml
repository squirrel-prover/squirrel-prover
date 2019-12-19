open Tactics
open Formula
open Term

type tac = Sequent.t Tactics.tac

module T = Prover.Prover_tactics

(** Propositional connectives *)

let goal_or_right_1 (s : Sequent.t) sk fk =
  match Sequent.get_conclusion s with
  | (Or (lformula, _)) -> sk
                            [Sequent.set_conclusion (lformula) s]
                            fk
  | _ -> fk (Tactics.Failure "Cannot introduce a disjunction")

let goal_or_right_2 (s : Sequent.t) sk fk =
  match Sequent.get_conclusion s with
  | (Or (_, rformula)) -> sk [Sequent.set_conclusion (rformula) s] fk
  | _ -> fk (Tactics.Failure "Cannot introduce a disjunction")

let () = T.register "left" goal_or_right_1
let () = T.register "right" goal_or_right_2

let goal_true_intro (s : Sequent.t) sk fk =
  match Sequent.get_conclusion s with
  | True -> sk [] fk
  | _ -> fk (Tactics.Failure "Cannot introduce true")

let () = T.register "true" goal_true_intro

let goal_and_right (s : Sequent.t) sk fk =
  match Sequent.get_conclusion s with
  | And (lformula, rformula) ->
    sk [ Sequent.set_conclusion (lformula) s;
         Sequent.set_conclusion (rformula) s ] fk
  | _ -> fk (Tactics.Failure "Cannot introduce a conjonction")

let () = T.register "split" goal_and_right

(** Compute the goal resulting from the addition of a list of
  * formulas as hypotheses,
  * followed by the left intro of existentials and conjunctions. *)
let rec left_introductions s = function
  | Formula.And (f,g) :: l -> left_introductions s (f::g::l)
  | Formula.Exists (vars,f) :: l ->
      let env = Sequent.get_env s in
      let subst,env =
        List.fold_left
          (fun (subst,env) v ->
             let env,v' =
               Vars.make_fresh env (Vars.var_type v) (Vars.name v)
             in
             let item =
               match Vars.var_type v with
                 | Vars.Index -> Term.Index (v,v')
                 | Vars.Timestamp -> Term.TS (Term.TVar v, Term.TVar v')
                 | Vars.Message -> Term.Term (Term.MVar v, Term.MVar v')
                 | Vars.Boolean -> Term.Term (Term.MVar v, Term.MVar v')
             in
               item::subst, env)
          ([],env)
          vars
      in
      let f = Formula.subst_formula subst f in
        left_introductions (Sequent.set_env env s) (f::l)
  | f :: l -> left_introductions (Sequent.add_formula f s) l
  | [] -> s

(** Introduce disjunction and implication (with conjunction on its left).
  * TODO this is a bit arbitrary, and it will be surprising for
  * users that "intro" does not introduce universal quantifiers. *)
let goal_intro (s : Sequent.t) sk fk =
  match Sequent.get_conclusion s with
  | ForAll (vs,f) ->
    let env = ref (Sequent.get_env s) in
    let vsubst =
      List.map
        (fun x ->
           (x, Vars.make_fresh_from_and_update env x))
        vs
    in
    let subst = Term.from_varsubst vsubst in
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
  | Atom (Message (Bformula.Neq,u,v)) ->
    let h = Message (Bformula.Eq,u,v) in
    let s' = Sequent.set_conclusion False s |> Sequent.add_formula (Atom h) in
    sk [s'] fk
  | _ ->
      fk (Tactics.Failure
            "Can only introduce implication, universal quantifications
             and disequality conclusions.")

let () = T.register "intro" goal_intro

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
    (fun l ->
       let ths =
         List.map
           (function
              | Prover.Theory tm -> tm
              | _ -> raise @@ Tactic_Hard_Failure "Improper arguments")
           l
       in
       goal_exists_intro ths)

let () =
  let open Prover.AST in
  let non_branching_intro =
    [ Abstract ("intro",[]) ;
      Abstract ("exists",[]) ;
      Abstract ("true",[]) ]
  in
  T.register_macro "intros"
    (Repeat (OrElse non_branching_intro)) ;
  T.register_macro "anyintro"
    (OrElse
       (Abstract ("split",[]) :: non_branching_intro))

(** Reasoning over constraints and messages *)

let constraints (s : Sequent.t) sk fk =
  if Sequent.constraints_valid s then
    sk [] fk
  else fk (Tactics.Failure "Constraints satisfiable")

let congruence (s : Sequent.t) sk fk =
  if Sequent.message_atoms_valid s then
    sk [] fk
  else fk (Tactics.Failure "Equations satisfiable")

let () = T.register "congruence" congruence

let () = T.register "constraints" constraints

let assumption (s : Sequent.t) sk fk =
  if Sequent.is_hypothesis (Sequent.get_conclusion s) s then
      sk [] fk
  else
    fk (Tactics.Failure "Conclusion is not an hypothesis")

let () = T.register "assumption" assumption

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

open Bformula

(** Eq-Indep Axioms *)

(* We include here rules that are specialization of the Eq-Indep axiom. *)

let eq_names (s : Sequent.t) sk fk =
  let s,trs = Sequent.get_trs s in
  let cnstrs = Completion.name_index_cnstrs trs
      (Sequent.get_all_terms s)
  in
  let s =
    List.fold_left (fun judge c ->
        Sequent.add_trace_formula c s
      ) s cnstrs
  in
  sk [s] fk

let () = T.register "eqnames" eq_names

let eq_constants fn (s : Sequent.t) sk fk =
  let s,trs = Sequent.get_trs s in
  let cnstrs =
    Completion.constant_index_cnstrs fn trs
      (Sequent.get_all_terms s)
  in
  let s =
    List.fold_left (fun s c ->
        Sequent.add_trace_formula c s
      ) s cnstrs
  in
  sk [s] fk

let () = T.register_fname "eqconstants" eq_constants

let eq_timestamps (s : Sequent.t) sk fk =
  let ts_classes = Sequent.get_ts_equalities s
                   |> List.map (List.sort_uniq Pervasives.compare)
  in
  let subst =
    let rec asubst e = function
        [] -> []
      | p::q -> TS (p,e) :: (asubst e q)
    in
    List.map (function [] -> [] | p::q -> asubst p q) ts_classes
    |> List.flatten
  in
  let terms = Sequent.get_all_terms s in
  let facts =
    List.fold_left
      (fun acc t ->
         let normt : Term.term = subst_term subst t in
         if normt = t then
           acc
         else
           Formula.Atom (Message (Eq, t, normt)) ::acc)
      [] terms
  in
  let s =
    List.fold_left
      (fun s c ->
         Sequent.add_formula c s)
      s facts
  in
  sk [s] fk

let () = T.register "eqtimestamps" eq_timestamps

(** EUF Axioms *)

(** [modulo_sym f at] applies [f] to [at] modulo symmetry of the equality. *)
let modulo_sym f at = match at with
  | (Eq as ord, t1, t2) | (Neq as ord, t1, t2) -> begin match f at with
      | Some _ as res -> res
      | None -> f (ord, t2, t1) end
  | _ -> f at

let euf_param (at : term_atom) = match at with
  | (Eq, Fun ((hash, _), [m; Name key]), s) ->
    if Theory.is_hash hash then
      Some (hash, key, m, s)
    else None
  | _ -> None

let euf_apply_schema sequent (_, (_, key_is), m, s) case =
  let open Euf in
  let open Process in
  (* We create the term equality *)
  let new_f = Formula.Atom (Message (Eq, case.message, m)) in
  (* Now, we need to add the timestamp constraints. *)
  (* The action name and the action timestamp variable are equal. *)
  let action_descr_ts = TName case.action_descr.action in
  (* The action occured before the test H(m,k) = s. *)
  let le_cnstr =
    List.map (fun ts ->
        Atom (Pts (Leq, action_descr_ts, ts))
      ) (Sequent.maximal_elems sequent (term_ts s @ term_ts m))
    |> mk_or_cnstr
  in
  (new_f, le_cnstr, case.env)

let euf_apply_direct theta (_, (_, key_is), m, _) dcase =
  let open Euf in
  let open Process in
  (* We create the term equality *)
  let eq = Formula.Atom (Message (Eq, dcase.d_message, m)) in
  (* Now, we need to add the timestamp constraint between [key_is] and
     [dcase.d_key_indices]. *)
  let eq_cnstr =
    List.map2 (fun i i' ->
        Atom (Pind (Eq, i, i'))
      ) key_is dcase.d_key_indices
    |> mk_and_cnstr
  in
  (eq, eq_cnstr)

(* TODO : make error reporting for euf more informative *)
let euf_apply_facts s at = match modulo_sym euf_param at with
  | None -> raise @@ Tactic_Hard_Failure "bad euf application"
  | Some p ->
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

let set_euf t = { Sequent.t_euf = true }

let euf_apply hypothesis_name (s : Sequent.t) sk fk =
  let s, at = Sequent.select_message_hypothesis hypothesis_name s set_euf in
  (* TODO: need to handle failure somewhere. *)
  sk (euf_apply_facts s at) fk

let () =
  T.register_general "euf"
    (function
      | [Prover.Theory (Theory.Var h)] -> euf_apply h
      | _ -> raise @@ Tactics.Tactic_Hard_Failure "improper arguments")

let apply id (ths:Theory.term list) (s : Sequent.t) =
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
    | f ->
        left_introductions s [f] ::
        List.rev subgoals
  in
  aux [] f

let apply id l s sk fk =
  match apply id l s with
    | l -> sk l fk
    | exception Failure s -> fk @@ Tactics.Failure s
    | exception _ -> fk @@ Tactics.Failure "failure"

let () =
  T.register_general "apply"
    (function
      | Prover.Goal_name id :: th_terms ->
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
  T.register_formula "assert" tac_assert

let collision_resistance (s : Sequent.t) sk fk =
  (* We collect all hashes appearing inside the hypotheses, and which satisfy
     the syntactic side condition. *)
  let hashes = List.filter
      (fun t -> match t with
         | Fun ((hash, _), [m; Name (key,ki)]) ->
           (Theory.is_hash hash) && (Euf.hash_key_ssc hash key [m])
         | _ -> false)
      (Sequent.get_all_terms s)
  in
  if List.length hashes = 0 then
    fk (Failure "no equality between hashes where the keys satisfiy the
 syntactic condition has been found")
  else
    begin
      let rec make_eq hash_list =
        match hash_list with
        | [] -> []
        | h1::q -> List.fold_left (fun acc h2 ->
            match h1, h2 with
            | Fun ((hash, _), [m1; Name key1]), Fun ((hash2, _), [m2; Name key2])
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
            | Fun ((hash, _), [m1; Name key1]), Fun ((hash2, _), [m2; Name key2])
              when hash = hash2 && key1 = key2 ->
              Formula.Atom (Message (Eq, m1, m2)) :: acc
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

let () = T.register "collision" collision_resistance
