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
(** The mode contains the information to modify the goal.
    Allows factorasation of the code between equivalence goals and deduction goals. *)
type mode = Equiv of Term.terms | Deduction of S.secrecy_goal


(*------------------------------------------------------------------*)
(** Get the mode from a sequent.
    Raise a soft failure if the sequent is not an equivalence or deduction goal. *)
let get_mode (s : ES.t) : mode =
  if S.conclusion_is_equiv s then
    Equiv (S.conclusion_as_equiv s)
  else if Library.Secrecy.is_loaded (ES.table s) then
    match S.get_secrecy_goal s with
    | Some goal -> 
      if Type.is_bitstring_encodable goal.right_ty then
        Deduction goal
      else
        soft_failure (Tactics.GoalBadShape
          "The right part of the (non-)deduction goal must be encodable")
    | None ->
      soft_failure (Tactics.GoalBadShape
        "expected an equivalence goal or a (non-)deduction goal with WeakSecrecy library")
  else
    soft_failure (Tactics.GoalBadShape
      "expected an equivalence goal or a (non-)deduction goal with WeakSecrecy library")

(** Get the list of terms contained in the goal. *)
let get_terms (mode : mode) : Term.terms =
  match mode with
  | Equiv terms -> terms
  | Deduction goal -> goal.left

(** Type the term given as argument to the tactic.
    Raise a soft failure if the function does not have the type [ty1 -> ty2]
    with both types encodable.
    Return the typed term, [ty1] and [ty2] *)
let convert_arg
    (term : Typing.term)
    (cenv : Typing.conv_env)
    : Term.term * Type.ty * Type.ty =
  let t, ty = Typing.convert cenv term in
  match ty with
  | Type.(Fun (ty1, ty2)) ->
    (** TODO : add support for oracles with multiple arguments *)
    if Type.is_bitstring_encodable ty1 && Type.is_bitstring_encodable ty2 then
      t, ty1, ty2
    else
      soft_failure (Failure "First argument must be a function with encodable types")
  | _ ->
    soft_failure (Failure "First argument must be a function")

(** Return the terms of the goal that have to be rewritten.
    Check that the type of this oracle is [ty]
    Get the term in postion [i] if [pos = Some i].
    Else, get the only oracle with the correct type or fails if there is not one possible choice.
    Return the term of the oracle and its position. *)
let get_oracle
    (pos : int L.located option)
    (ty : Type.ty)
    (mode : mode) :
    Term.term * int =
  let terms = get_terms mode in
  match pos with
  | Some i ->
    if (L.unloc i) < 0 || (L.unloc i) >= List.length terms then
      soft_failure ~loc:(L.loc i) (GoalBadShape "Wrong number of equivalence item");
    let oracle = List.nth terms (L.unloc i) in
    let oracle_ty = Term.ty oracle in
    if not (Type.equal oracle_ty ty) then
      soft_failure (Failure "The given item in the goal must have the same type than the argument");
    oracle, L.unloc i
  | None ->
    let terms_with_pos = List.mapi (fun i t -> t, i) terms in
    let oracles = List.filter (fun (t,_) -> Term.ty t = ty) terms_with_pos in
    match oracles with
    | [] -> soft_failure (Failure "The goal does not contains a function with the same type as the argument.")
    | [oracle, i] -> oracle, i 
    | _ -> soft_failure (Failure "The goal contains several functions with the same type as the argument.\nPrecise the position of the oracle you want to rewrite.")

(** Return a new sequent corresponding to [s]
    with the oracle in position [i] replaced by [new_oracle]*)
let mk_maingoal
    (oracle_new : Term.term)
    (mode : mode)
    (i : int)
    (s : ES.t) : ES.t
  =
  match mode with
  | Equiv terms ->
    let terms_new = List.mapi
      (fun j t -> if j = i then oracle_new else t)
      terms
    in
    S.set_equiv_conclusion terms_new s
  | Deduction goal ->
    let terms_new = List.mapi
      (fun j t -> if j = i then oracle_new else t)
      goal.left
    in
    let goal_new = { goal with left = terms_new } in
    let conc = S.mk_secrecy_concl goal_new s in
    S.set_conclusion conc s

(** Return a sequent for the side condition to prove to use [rewrite oracle].
    Intuitively, the user has to prove that [oracle_old] and [oracle_new]
    retuns the same result for any input computable with the terms contained
    in [mode].*)
let mk_subgoal
    (oracle_old : Term.term)
    (oracle_new : Term.term)
    (mode : mode)
    (input_ty : Type.ty)
    (s : ES.t) : ES.t
  =
  let terms = get_terms mode in
  let ty =
    if List.length terms = 1 then
      Term.ty (List.hd terms)
    else
      Tuple (List.map Term.ty terms)
  in
  let f_ty = Type.(Fun (ty, input_ty)) in
  let _, f_var = Vars.make_global `Approx (ES.vars s) f_ty "f" in
  let mk_term oracle =
    let term = 
      if List.length terms = 1 then
        List.hd terms
      else
        Term.mk_tuple terms
    in
    Term.(mk_app oracle [mk_app (mk_var f_var) [term]])
  in
  let loc_form = Term.mk_eq (mk_term oracle_old) (mk_term oracle_new) in
  let glob_form = Equiv.(Quant (ForAll,
                                [f_var, Vars.Tag.make ~adv:true Global], (*TODO check if we must have [glob] tag*)
                                Atom (Reach loc_form))) in
  S.set_conclusion glob_form s

(** Parse the argument of the tactic and return the two new sequent to prove.*)
let rewrite_oracle_args (args : Args.parser_arg list) (s : ES.t) : ES.t list =
  match args with
  | [Args.RewriteOracle (term, pos_opt)] -> 
    let mode = get_mode s in
    let cenv = Typing.{ env = ES.env s; cntxt = InGoal; } in
    (**TODO : check if [InGoal] is correct*)
    let oracle_new, ty1, ty2 = convert_arg term cenv in
    let oracle_old, i = get_oracle pos_opt (Type.Fun (ty1,ty2)) mode in
    let maingoal = mk_maingoal oracle_new mode i s in
    let subgoal = mk_subgoal oracle_old oracle_new mode ty1 s in
    [subgoal; maingoal]
  | _ -> hard_failure (Failure "improper arguments")

(** Declare the tactic. *)
let rewrite_oracle_tac args s sk fk =
  try sk (rewrite_oracle_args args s) fk with
  | Tactics.Tactic_soft_failure e -> fk e

(*------------------------------------------------------------------*)
let () =
  T.register_general "rewrite oracle"
    ~pq_sound:false
    (LT.gentac_of_etac_arg rewrite_oracle_tac)