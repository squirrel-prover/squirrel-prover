(** Tactics exploiting a name's freshness. *)
open Squirrelcore

module ES = EquivSequent

module T = ProverTactics
module LT = LowTactics

module L = Location
module Args = HighTacticsArgs

module S = LowEquivSequent

(*------------------------------------------------------------------*)
let soft_failure = Tactics.soft_failure
let hard_failure = Tactics.hard_failure

(*------------------------------------------------------------------*)
let check_goal (pos : int L.located option) (s : ES.t) =
  if not (S.conclusion_is_equiv s) then
    hard_failure (GoalBadShape "Goal must be an equivalence");
  let equiv = S.conclusion_as_equiv s in
  match pos with
  | Some i -> if (L.unloc i < 0 || List.length equiv <= L.unloc i) then
      soft_failure ~loc:(L.loc i) (GoalBadShape "Wrong number of equivalence item")
  | None -> ()

let convert_arg (term : Typing.term) (s : ES.t) : Term.term * Type.ty =
  let cenv = Typing.{ env = ES.env s; cntxt = InGoal; } in (**TODO : check if [InGoal] is correct*)
  let t, ty = Typing.convert cenv term in
  match ty with
  | Type.(Fun (Message, Message)) -> t, ty
  | _ ->
    soft_failure (Failure "First argument must be a function")

let get_oracle
    (pos : int L.located option)
    (ty : Type.ty)
    (s : ES.t) : Term.term * int =
  let terms = S.conclusion_as_equiv s in
  match pos with
  | Some i -> 
    let oracle = List.nth terms (L.unloc i) in
    let oracle_ty = Term.ty oracle in
    if not (Type.equal oracle_ty ty) then
      soft_failure (Failure "The item in the equivalence must be typed [message -> message]");
    oracle, L.unloc i
  | None ->
    let terms_with_pos = List.mapi (fun i t -> t, i) terms in
    let oracles = List.filter (fun (t,_) -> Term.ty t = ty) terms_with_pos in
    match oracles with
    | [] -> soft_failure (Failure "The goal does not contains a function with the same type as the argument.")
    | [oracle, i] -> oracle, i 
    | _ -> soft_failure (Failure "The goal contains several functions with the same type as the argument.\nPrecise the position of the oracle you want to rewrite.")


let mk_maingoal
    (oracle_new : Term.term)
    (i : int)
    (s : ES.t) : ES.t
  =
  let equiv = S.conclusion_as_equiv s in
  let equiv_new = List.mapi
    (fun j t -> if j = i then oracle_new else t)
    equiv
  in
  S.set_equiv_conclusion equiv_new s

let mk_subgoal
    (oracle_old : Term.term)
    (oracle_new : Term.term)
    (s : ES.t) : ES.t
  =
  let equiv = S.conclusion_as_equiv s in
  let f_ty = Type.(Fun (Tuple (List.map Term.ty equiv), Message)) in (*FIXME : Problem if one element*)
  let _, f_var = Vars.make_global `Approx (ES.vars s) f_ty "f" in
  let mk_term oracle =
    Term.(mk_app oracle [mk_app (mk_var f_var) [(mk_tuple equiv)]])
  in
  let loc_form = Term.mk_eq (mk_term oracle_old) (mk_term oracle_new) in
  let glob_form = Equiv.(Quant (ForAll,
                                [f_var, Vars.Tag.make ~adv:true Global], (*TODO check if we must have [glob] tag*)
                                Atom (Reach loc_form))) in
  S.set_conclusion glob_form s

let rewrite_oracle_args (args : Args.parser_arg list) s : ES.t list =
  match args with
  | [Args.RewriteOracle (term, pos_opt)] -> 
    check_goal pos_opt s;
    let oracle_new, ty = convert_arg term s in
    let oracle_old, i = get_oracle pos_opt ty s in
    let maingoal = mk_maingoal oracle_new i s in
    let subgoal = mk_subgoal oracle_old oracle_new s in
    [subgoal; maingoal]
  | _ -> hard_failure (Failure "improper arguments")

let rewrite_oracle_tac args s sk fk =
  try sk (rewrite_oracle_args args s) fk with
  | Tactics.Tactic_soft_failure e -> fk e

(*------------------------------------------------------------------*)
let () =
  T.register_general "rewrite oracle"
    ~pq_sound:false
    (LT.gentac_of_etac_arg rewrite_oracle_tac)