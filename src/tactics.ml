open Logic
open Term

type 'a fk = unit -> 'a

type ('a,'b) sk = 'a -> 'b fk -> 'b

type 'a tac =
  Judgment.t -> (Judgment.t list,'a) sk -> 'a fk -> 'a

let remove_finished judges =
  List.filter
    (fun j ->
       match j.Judgment.goal with
       | Unit -> false
       | _ -> true)
    judges

let simplify j =
  match j.Judgment.goal with
  | Postcond p when p.evars = [] ->
    Judgment.set_goal (Fact p.efact) j
  | Fact True -> Judgment.set_goal Unit j
  | _ -> j

(** Basic Tactics *)

let tact_wrap f v sk fk = sk (f v) fk

let tact_return a v = a v (fun r fk' -> r) (fun _ -> raise @@ Failure "return")

let tact_andthen a b sk fk v = a v (fun v fk' -> b v sk fk') fk

let tact_orelse a b v sk fk = a v sk (fun () -> b v sk fk)

let repeat t j sk fk =
  let rec success_loop oldj v fk' =
    match v with
    | [a] when a = oldj -> sk v fk
    | [b] -> t b (success_loop b) (fun _ -> sk v fk)
    | _ -> raise @@ Failure "cannot repeat a tactic creating subgoals"
  in
  t j (success_loop j) fk


let lift =
  fun tac vs sk fk ->
  let exception Suc_fail in
  let comp_vs' () =
    List.fold_left (fun acc v ->
        tac v (fun l _ -> l) (fun () -> raise Suc_fail)
        @ acc
      ) [] vs
  in
  (* We catch the exception before calling the continuation. *)
  let opt_vs' = try Some (comp_vs' ()) with Suc_fail -> None in
  match opt_vs' with
  | Some vs' -> sk vs' fk
  | None -> fk ()

(** Introduction Rules *)

let goal_or_intro_l (judge : Judgment.t) sk fk =
  match Judgment.get_goal_fact judge with
  | Or (lgoal, _) -> sk [Judgment.set_goal_fact lgoal judge] fk
  | _ -> raise @@ Failure "goal ill-formed"

let goal_or_intro_r (judge : Judgment.t) sk fk =
  match Judgment.get_goal_fact judge with
  | Or (_, rgoal) -> sk [Judgment.set_goal_fact rgoal judge] fk
  | _ -> raise @@ Failure "goal ill-formed"

(** To prove phi \/ psi, try first to prove phi and then psi *)
let goal_or_intro (judge : Judgment.t) sk fk =
  tact_orelse goal_or_intro_l goal_or_intro_r judge sk fk

let goal_true_intro (judge : Judgment.t) sk fk =
  match Judgment.get_goal_fact judge with
  | True -> sk () fk
  | _ -> raise @@ Failure "goal ill-formed"

let goal_and_intro (judge : Judgment.t) sk fk =
  match Judgment.get_goal_fact judge with
  | And (lgoal,rgoal) ->
    sk [ Judgment.set_goal_fact lgoal judge;
         Judgment.set_goal_fact rgoal judge ] fk
  | _ -> raise @@ Failure "goal ill-formed"

(** Introduce the universally quantified variables and the goal. *)
let goal_forall_intro (judge : Judgment.t) sk fk =
  let jgoal = Judgment.get_goal_formula judge in
  let vsubst =
    List.fold_left
      (fun subst x ->
         if List.mem x judge.Judgment.vars then
           (x, make_fresh_of_type x):: subst
         else
           (x, x)::subst ) [] jgoal.uvars
  in
  let subst = from_fvarsubst vsubst in
  let new_cnstr = subst_constr subst jgoal.uconstr
  and new_fact = subst_fact subst jgoal.ufact
  and new_goals =
    List.map
      (fun goal ->
         Postcond (subst_postcond subst goal))
      jgoal.postcond
  in
  let judges =
    List.map (fun goal ->
        Judgment.set_goal goal judge
        |> Judgment.add_vars @@ List.map snd vsubst
        |> Judgment.add_fact new_fact
        |> Judgment.add_constr new_cnstr
      ) new_goals
  in
  sk (List.map simplify judges) fk

let goal_exists_intro nu (judge : Judgment.t) sk fk =
  let jgoal = Judgment.get_goal_postcond judge in
  let pc_constr = subst_constr nu jgoal.econstr in
  let judge =
    Judgment.set_goal
      (Fact (subst_fact nu jgoal.efact)) judge
    |> Judgment.add_constr (Not pc_constr)
  in
  sk [judge] fk

let goal_intro (judge : Judgment.t) sk fk =
  match Judgment.get_goal_fact judge with
  | False -> sk [judge] fk
  | f -> let judge = Judgment.add_fact (Not (f)) judge
                     |> Judgment.set_goal_fact False
    in
    sk [judge] fk

let goal_any_intro (judge : Judgment.t) sk fk =
  match judge.Judgment.goal with
  | Formula _ -> goal_forall_intro judge sk fk
  | Fact _ -> goal_intro judge sk fk
  | _ -> fk ()

let fail_goal_false (judge : Judgment.t) sk fk =
  match Judgment.get_goal_fact judge with
  | False -> fk ()
  | _ -> raise @@ Failure "goal ill-formed"

let constr_absurd (judge : Judgment.t) sk fk =
  if not @@ Theta.is_sat judge.Judgment.theta then
    sk [] fk
  else fk ()

let gamma_absurd (judge : Judgment.t) sk fk =
  if not @@ Gamma.is_sat judge.Judgment.gamma then
    sk [] fk
  else fk ()

let or_to_list f =
  let rec aux acc = function
    | Or (g, h) -> aux (aux acc g) h
    | _ as a -> a :: acc
  in
  (* Remark that we simplify the formula. *)
  aux [] (simpl_fact f)

let gamma_or_intro (judge : Judgment.t) sk fk select_pred =
  let sel, nsel =
    Utils.List.split_pred select_pred
      (Gamma.get_facts judge.Judgment.gamma)
  in
  let rec mk_facts acc = function
    | [] -> [acc]
    | l :: ors -> List.map (fun x -> mk_facts (x :: acc) ors) l
                  |> List.flatten
  in
  let judges =
    mk_facts [] (List.map or_to_list sel)
    |> List.map (fun fs ->
        Judgment.set_gamma
          (Gamma.set_facts judge.Judgment.gamma (fs @ nsel))
          judge )
  in
  sk judges fk

(** Utils *)
let mk_or_cnstr l = match l with
  | [] -> False
  | [a] -> a
  | a :: l' ->
    let rec mk_c acc = function
      | [] -> acc
      | x :: l -> mk_c (Or (x,acc)) l in
    mk_c a l'

let mk_and_cnstr l = match l with
  | [] -> True
  | [a] -> a
  | a :: l' ->
    let rec mk_c acc = function
      | [] -> acc
      | x :: l -> mk_c (And (x,acc)) l in
    mk_c a l'


(** Eq-Indep Axioms *)

(* We include here rules that are specialization of the Eq-Indep axiom. *)

let eq_names (judge : Judgment.t) sk fk =
  let judge = Judgment.update_trs judge in
  let cnstrs = Completion.name_index_cnstrs (Gamma.get_trs judge.Judgment.gamma)
      (Gamma.get_all_terms judge.Judgment.gamma)
  in
  let judge =
    List.fold_left (fun judge c ->
        Judgment.add_constr c judge
      ) judge cnstrs
  in
  sk [judge] fk

let eq_constants fn (judge : Judgment.t) sk fk =
  let judge = Judgment.update_trs judge in
  let cnstrs =
    Completion.constant_index_cnstrs fn (Gamma.get_trs judge.Judgment.gamma)
      (Gamma.get_all_terms judge.Judgment.gamma)
  in
  let judge =
    List.fold_left (fun judge c ->
        Judgment.add_constr c judge
      ) judge cnstrs
  in
  sk [judge] fk

let eq_timestamps (judge : Judgment.t) sk fk =
  let ts_classes = Theta.get_equalities judge.Judgment.theta
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
  let terms = (Gamma.get_all_terms judge.Judgment.gamma) in
  let facts =
    List.fold_left
      (fun acc t ->
         let normt = subst_term subst t in
         if normt = t then
           acc
         else
           Atom (Eq, t, normt) ::acc )
      [] terms
  in
  let judge =
    List.fold_left
      (fun judge c ->
         Judgment.add_fact c judge)
      judge facts
  in
  sk [judge] fk

(** EUF Axioms *)

(** [modulo_sym f at] applies [f] to [at] modulo symmetry of the equality. *)
let modulo_sym f at = match at with
  | (Eq as ord, t1, t2) | (Neq as ord, t1, t2) -> begin match f at with
      | Some _ as res -> res
      | None -> f (ord, t2, t1) end
  | _ -> f at

let euf_param (at : atom) = match at with
  | (Eq, Fun ((hash, _), [m; Name key]), s) ->
    if Theory.is_hash hash then
      Some (hash, key, m, s)
    else None
  | _ -> None

let euf_apply_schema theta (_, (_, key_is), m, s) case =
  let open Euf in
  let open Process in
  (* We create the term equality *)
  let eq = Atom (Eq, case.message, m) in
  let new_f = And (eq, case.blk_descr.condition) in
  (* Now, we need to add the timestamp constraints. *)
  (* The block action name and the block timestamp variable are equal. *)
  let blk_ts = TName case.blk_descr.action in
  (* The block occured before the test H(m,k) = s. *)
  let le_cnstr =
    List.map (fun ts ->
        Atom (Pts (Leq, blk_ts, ts))
      ) (Theta.maximal_elems theta (term_ts s @ term_ts m))
    |> mk_or_cnstr
  in
  (* The key indices in the bock and when m was hashed are the same. *)
  let eq_cnstr =
    List.map2 (fun i i' ->
        Atom (Pind (Eq, i, i'))
      ) key_is case.key_indices
    |> mk_and_cnstr
  in
  let constr = And (eq_cnstr, le_cnstr) in
  (new_f, constr)


let euf_apply_direct theta (_, (_, key_is), m, _) dcase =
  let open Euf in
  let open Process in
  (* We create the term equality *)
  let eq = Atom (Eq, dcase.d_message, m) in
  (* Now, we need to add the timestamp constraint between [key_is] and
     [dcase.d_key_indices]. *)
  let eq_cnstr =
    List.map2 (fun i i' ->
        Atom (Pind (Eq, i, i'))
      ) key_is dcase.d_key_indices
    |> mk_and_cnstr
  in
  (eq, eq_cnstr)

let euf_apply_facts judge at = match modulo_sym euf_param at with
  | None -> raise @@ Failure "bad euf application"
  | Some p ->
    let (hash_fn, (key_n, key_is), m, s) = p in
    let rule = Euf.mk_rule m s hash_fn key_n in
    let schemata_premises =
      List.map (fun case ->
          let new_f, new_cnstr = euf_apply_schema judge.Judgment.theta p case in
          Judgment.add_fact new_f judge
          |> Judgment.add_constr new_cnstr
          |> Judgment.add_indices case.Euf.blk_descr.Process.indices
        ) rule.Euf.case_schemata
    and direct_premises =
      List.map (fun case ->
          let new_f, new_cnstr = euf_apply_direct judge.Judgment.theta p case in
          Judgment.add_fact new_f judge
          |> Judgment.add_constr new_cnstr
        ) rule.Euf.cases_direct
    in
    schemata_premises @ direct_premises

let euf_apply f_select (judge : Judgment.t) sk fk =
  let g, at = Gamma.select judge.Judgment.gamma f_select (set_euf true) in
  let judge = Judgment.set_gamma g judge in
  (* TODO: need to handle failure somewhere. *)
  sk (euf_apply_facts judge at) fk

let apply gp (subst:subst) (judge : Judgment.t) sk fk =
  (* We first check if constr is satisfied *)
  let new_constr = subst_constr subst gp.uconstr in
  let rec to_cnf c = match c with
    | Atom a -> [a]
    | True -> []
    | And (a, b) -> (to_cnf a) @ (to_cnf b)
    | _ -> raise @@ Failure
        "Can only apply axiom with constraints restricted to conjunctions."
  in
  let tatom_list = to_cnf new_constr in
  if not( Theta.is_valid judge.Judgment.theta tatom_list) then
    raise @@ Failure "Constraint on the variables not satisfied.";
  (* The precondition creates a new subgoal *)
  let new_judge =
    Judgment.set_goal (Fact (subst_fact subst gp.ufact)) judge
    |> simplify
  in
  let new_truths =
    List.map (fun goal ->
        let goal = fresh_postcond goal in
        subst_postcond subst goal
      ) gp.postcond
  in
  let judge =
    List.fold_left (fun judge nt ->
        Judgment.add_fact nt.efact judge
        |> Judgment.add_constr nt.econstr
        |> Judgment.add_vars nt.evars
      ) judge new_truths
  in
  sk [new_judge; judge] fk
