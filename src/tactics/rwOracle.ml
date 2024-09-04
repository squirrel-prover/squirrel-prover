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
type mode = EquivAsymp of Term.terms | Deduction of S.secrecy_goal

(** Get the mode from a sequent.
    Raise a soft failure if the sequent is not an equivalence or deduction goal. *)
let get_mode (s : ES.t) : mode =
  let bad_goal () =
    soft_failure
      (Tactics.GoalBadShape
         "expected an equivalence goal or a (non-)deduction goal");
  in
  
  if S.conclusion_is_equiv s then begin
    let concl = S.conclusion_as_equiv s in
    if concl.bound <> None then
      soft_failure
        (Tactics.GoalBadShape "expected an asymptotic equivalence goal");

    EquivAsymp concl.terms
  end
  else begin
    if not (Library.Secrecy.is_loaded (ES.table s)) then bad_goal ();

    match S.get_secrecy_goal s with
    | Some goal -> 
      if not (Type.is_bitstring_encodable goal.right_ty) then
        soft_failure
          (Tactics.GoalBadShape
             "The right part of the (non-)deduction goal must be bistring encodable");
      
      Deduction goal
        
    | None -> bad_goal ()
  end

(** Get the list of terms contained in the goal. *)
let get_terms (mode : mode) : Term.terms =
  match mode with
  | EquivAsymp terms -> terms
  | Deduction goal -> goal.left

(*------------------------------------------------------------------*)
(** Arguments *)

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
    (* TODO : add support for oracles with multiple arguments *)
    if Type.is_bitstring_encodable ty1 && Type.is_bitstring_encodable ty2 then
      t, ty1, ty2
    else
      soft_failure (Failure "First argument must be a function with encodable types")
  | _ ->
    soft_failure (Failure "First argument must be a function")

(** Parse the [named_arg] to know if it is ~reversed (returns true) or empty (returns false).
    Raises a soft filure otherwise *)
let parse_named_args : Args.named_args -> bool = function
  | [] -> false
  | [NArg lsymb] when L.unloc lsymb = "reverse" -> true
  | _ -> soft_failure (Failure "Wrong named argument.@.rewrite oracle only accepts ~reverse.")

(*------------------------------------------------------------------*)

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
  | EquivAsymp terms ->
    let terms_new = 
      List.mapi
        (fun j t -> if j = i then oracle_new else t)
        terms
    in
    S.set_equiv_conclusion { terms = terms_new; bound = None; } s

  | Deduction goal ->
    let terms_new =
      List.mapi
        (fun j t -> if j = i then oracle_new else t)
        goal.left
    in
    let goal_new = { goal with left = terms_new } in
    let conc = S.mk_secrecy_concl goal_new s in
    S.set_conclusion conc s

(** Return the argument of symbols f in the subgoal.
    It get the terms in [mode], in a tuple if there are more than one.
    If [reverse] is true, it replace the [i]-th term with [new_oracle] *)
let get_f_arg
    (mode : mode)
    (reverse : bool)
    (i : int)
    (oracle_new : Term.term) : Term.term
  =
  let terms_init = get_terms mode in
  let terms =
    if reverse then
      List.mapi (fun j t -> if i=j then oracle_new else t) terms_init
    else
      terms_init
  in
  match terms with
  | [] -> assert false
  | [t] -> t
  | _ -> Term.mk_tuple terms

(** Return a sequent for the side condition to prove to use [rewrite oracle].
    Intuitively, the user has to prove that [oracle_old] and [oracle_new]
    retuns the same result for any input computable with the terms contained
    in [mode].*)
let mk_subgoal
    (oracle_old : Term.term)
    (oracle_new : Term.term)
    (mode : mode)
    (reverse : bool)
    (i : int)
    (input_ty : Type.ty)
    (s : ES.t) : ES.t
  =
  let f_arg = get_f_arg mode reverse i oracle_new in
  let ty = Term.ty f_arg in
  let f_ty = Type.(Fun (ty, input_ty)) in
  let _, f_var = Vars.make_global `Approx (ES.vars s) f_ty "f" in
  let mk_term oracle =
    Term.(mk_app oracle [mk_app (mk_var f_var) [f_arg]])
  in
  let loc_form = Term.mk_eq (mk_term oracle_old) (mk_term oracle_new) in
  let glob_form = 
    Equiv.mk_quant_tagged Equiv.ForAll
      [f_var, Vars.Tag.make ~adv:true Global]
      (Equiv.Atom (Reach { formula = loc_form; bound = None; }))
  in
  S.set_conclusion glob_form s

(** Parse the argument of the tactic and return the two new sequent to prove.*)
let rewrite_oracle_args (args : Args.parser_arg list) (s : ES.t) : ES.t list =
  match args with
  | [Args.RewriteOracle (term, named_args, pos_opt)] -> 
    let reverse = parse_named_args named_args in
    let mode = get_mode s in
    let cenv = Typing.{ env = ES.env s; cntxt = InGoal; } in
    let oracle_new, ty1, ty2 = convert_arg term cenv in
    let oracle_old, i = get_oracle pos_opt (Type.Fun (ty1,ty2)) mode in
    let maingoal = mk_maingoal oracle_new mode i s in
    let subgoal = mk_subgoal oracle_old oracle_new mode reverse i ty1 s in
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
