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
let check_goal (i : int L.located) (s : ES.t) =
  if not (S.conclusion_is_equiv s) then
    hard_failure (GoalBadShape "Goal must be an equivalence");
  let equiv = S.conclusion_as_equiv s in
  if (L.unloc i < 0 || List.length equiv <= L.unloc i) then
    soft_failure ~loc:(L.loc i) (GoalBadShape "Wrong number of equivalence item")

let get_oracle (i : int L.located) (s : ES.t) =
  let equiv = S.conclusion_as_equiv s in
  if Term.ty (List.nth equiv (L.unloc i)) <> Type.(Fun (Message, Message)) then
    soft_failure (Failure "The item in the equivalence must be typed [message -> message]");
  List.nth equiv (L.unloc i)

let convert_arg (term : Typing.term) (s : ES.t) =
  let cenv = Typing.{ env = ES.env s; cntxt = InGoal; } in (**TODO : check if [InGoal] is correct*)
  let t, ty = Typing.convert cenv term in
  match t, ty with
  | Term.(Quant (Lambda, _, _)), Type.(Fun (Message, Message)) ->
    t
  | Term.(Quant (Lambda, _, _)), _ ->
    soft_failure (Failure "First argument must be typed [message -> message]")
  | _, _ ->
    soft_failure (Failure "First argument must be a function")

let mk_maingoal
    (oracle_new : Term.term)
    (i : int L.located)
    (s : ES.t) : ES.t
  =
  let equiv = S.conclusion_as_equiv s in
  let equiv_new = List.mapi (fun j t -> if j = L.unloc i then oracle_new else t) equiv in
  S.set_equiv_conclusion equiv_new s

let mk_subgoal
    (oracle_old : Term.term)
    (oracle_new : Term.term)
    (s : ES.t) : ES.t
  =
  let equiv = S.conclusion_as_equiv s in
  let f_ty = Type.(Fun (Tuple (List.map Term.ty equiv), Message)) in (*FIXME : Proble if one element*)
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
  | [Args.RewriteOracle (term, i)] -> 
    check_goal i s;
    let oracle_old = get_oracle i s in
    let oracle_new = convert_arg term s in
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