(** Tactic allowing to modify an oracle in a non-deduction goal. *)
open Squirrelcore

module ES = EquivSequent
module SE = SystemExpr
module CP = ComputePredicates

module T = ProverTactics
module LT = LowTactics

module L = Location
module Args = HighTacticsArgs


(*------------------------------------------------------------------*)
let soft_failure = Tactics.soft_failure
let hard_failure = Tactics.hard_failure

(*------------------------------------------------------------------*)
(** The mode describes whether the goal is an equiv or a secrecy goal.
    Allows factorisation of the code. *)
type mode = EquivAsymp of Equiv.equiv | Deduction of CP.form

(** Gets the mode from a sequent.
    Raises a soft failure if the sequent is not
    an equivalence or deduction goal. *)
let get_mode (s : ES.t) : mode =
  if ES.conclusion_is_equiv s then
    begin
      let concl = ES.conclusion_as_equiv s in
      if concl.bound <> None then
        soft_failure
          (Tactics.GoalBadShape "expected an asymptotic equivalence goal");
      
      EquivAsymp concl
    end
  else if ES.conclusion_is_computability s then
    begin
      let concl = ES.conclusion_as_computability s in
      let ty_right = Term.ty (CP.right concl) in
      if not (Type.is_bitstring_encodable ty_right) then
        soft_failure
          (Tactics.GoalBadShape
             "The right part of the (non-)deduction goal \
              must be bistring encodable");
      Deduction concl
    end
  else 
    soft_failure
      (Tactics.GoalBadShape
         "expected an equivalence goal or a (non-)deduction goal")

(** Gets the list of terms contained in the goal. *)
let get_terms (mode : mode) : Term.terms =
  match mode with
  | EquivAsymp equiv -> equiv.terms
  | Deduction goal -> CP.lefts goal


(*------------------------------------------------------------------*)
(** Arguments *)

(** Types the term given as argument to the tactic.
    Raises a soft failure if the function does not have the type [ty1 -> ty2]
    with both types encodable.
    Returns the typed term, [ty1], and [ty2] *)
let convert_arg
    (term : Typing.term)
    (cenv : Typing.conv_env)
    : Term.term * Type.ty * Type.ty =
  let t, ty = Typing.convert cenv term in
  match ty with
  | Type.(Fun (ty1, ty2)) ->
    (* TODO: add support for oracles with multiple arguments *)
    if Type.is_bitstring_encodable ty1 && Type.is_bitstring_encodable ty2 then
      t, ty1, ty2
    else
      soft_failure 
        (Failure "First argument must be a function with encodable types")
  | _ -> soft_failure (Failure "First argument must be a function")

(** Parses the [named_arg] to know if it is [~reversed] (returns [true])
    or empty (returns [false]).
    Raises a soft failure otherwise *)
let parse_named_args : Args.named_args -> bool = function
  | [] -> false
  | [NArg lsymb] when L.unloc lsymb = "reverse" -> true
  | _ -> soft_failure (Failure "Wrong named argument.@.rewrite \
                                oracle only accepts ~reverse.")

(*------------------------------------------------------------------*)

(** Computes the term of the goal that has to be rewritten.
    Ensures that the type of the oracle to rewrite is [ty]
    Gets the term in postion [i] if [pos = Some i].
    Otherwise, gets the only oracle with the correct type,
    or fails if there is not exactly one possible choice.
    Returns the oracle and its position. *)
let get_oracle
    (pos : int L.located option)
    (ty : Type.ty)
    (mode : mode)
    : Term.term * int =
  let terms = get_terms mode in
  match pos with
  | Some i ->
    if (L.unloc i) < 0 || (L.unloc i) >= List.length terms then
      soft_failure ~loc:(L.loc i) 
        (GoalBadShape "Wrong number of equivalence items.");
    let oracle = List.nth terms (L.unloc i) in
    let oracle_ty = Term.ty oracle in
    if not (Type.equal oracle_ty ty) then
      soft_failure (Failure "The given item in the goal \
                             must have the same type as the argument.");
    oracle, L.unloc i

  | None ->
     let terms_with_pos = List.mapi (fun i t -> t, i) terms in
     let oracles = List.filter (fun (t,_) -> Term.ty t = ty) terms_with_pos in
     match oracles with
     | [] -> soft_failure (Failure "The goal does not contain \
                                    a function with the same type as \
                                    the argument.")
     | [oracle, i] -> oracle, i 
     | _ -> soft_failure (Failure "The goal contains several functions \
                                   with the same type as the argument.\n\
                                   Please specify the position of the oracle \
                                   you want to rewrite.")


(** Returns a new sequent, which is [s] where the oracle
    in position [i] has been replaced with [new_oracle] *)
let mk_maingoal
      ~(new_oracle : Term.term)
      (mode : mode)
      (i : int)
      (s : ES.t) : ES.t
  =
  let old_terms = get_terms mode in
  let new_terms =
    List.mapi (fun j t -> if j = i then new_oracle else t) old_terms
  in

  match mode with
  | EquivAsymp equiv ->
     ES.set_equiv_conclusion {equiv with terms = new_terms} s

  | Deduction goal ->
     let new_goal = CP.update_lefts new_terms goal in
     ES.set_conclusion (CP.to_global new_goal) s


(** Returns the term to be used as argument of the adversarial function [f]
    introduced in the subgoal.
    We take all terms in [mode], and construct a tuple 
    if there are more than one.
    If [reverse] is set to [true], replaces the [i]-th term with [new_oracle] *)
let subgoal_f_arg
    (mode : mode)
    (reverse : bool)
    (i : int)
    ~(new_oracle : Term.term) 
    : Term.term =
  let terms_init = get_terms mode in
  let terms =
    if reverse then
      List.mapi (fun j t -> if i=j then new_oracle else t) terms_init
    else
      terms_init
  in
  Term.mk_tuple terms


(** Returns the proof obligation expressing the side condition 
    of the rule [rewrite oracle].
    Intuitively, the user has to prove that [old_oracle] and [new_oracle]
    return the same result for any input computable from the terms contained
    in [mode] (or, if [reverse], from these terms and [new_oracle]). *)
let mk_subgoal
    ~(old_oracle : Term.term)
    ~(new_oracle : Term.term)
    (mode : mode)
    (reverse : bool)
    (i : int)
    (input_ty : Type.ty)
    (s : ES.t) : ES.t
  =
  let system =
    match mode with
    | EquivAsymp _ -> (Utils.oget (ES.env s).system.pair :> SystemExpr.fset)
    | Deduction g ->
      let system = CP.system g in
      if not (SE.is_fset system) then
        soft_failure (Failure "the conclusion must be over a concrete system");
      SE.to_fset system 
  in
  let system = (system :> SystemExpr.arbitrary) in
  let f_arg = subgoal_f_arg mode reverse i ~new_oracle in
  let ty = Term.ty f_arg in
  let f_ty = Type.func ty input_ty in
  let _, f_var = Vars.make_global `Approx (ES.vars s) f_ty "f" in
  let mk_term oracle =
    Term.(mk_app oracle [mk_app (mk_var f_var) [f_arg]])
  in
  let loc_form = Term.mk_eq (mk_term old_oracle) (mk_term new_oracle) in
  let glob_form = 
    Equiv.mk_quant_tagged Equiv.ForAll
      [f_var, Vars.Tag.make ~adv:true Global]
      (Equiv.Atom (Reach { formula = loc_form; bound = None; }))
  in
  ES.set_conclusion_in_context
    {(ES.env s).system with set=system}
    glob_form s


(** Parses the arguments of the tactic, and 
    returns the remaining sequent as well as the generated subgoal. *)
let rewrite_oracle_args (args : Args.parser_arg list) (s : ES.t) : ES.t list =
  match args with
  | [Args.RewriteOracle (term, named_args, pos_opt)] -> 
     let reverse = parse_named_args named_args in
     let mode = get_mode s in
     let cenv = Typing.{ env = ES.env s; cntxt = InGoal; } in
     let new_oracle, ty1, ty2 = convert_arg term cenv in
     let old_oracle, i = get_oracle pos_opt (Type.func ty1 ty2) mode in
     let maingoal = mk_maingoal ~new_oracle mode i s in
     let subgoal = 
       mk_subgoal ~old_oracle ~new_oracle mode reverse i ty1 s 
     in
     [subgoal; maingoal]
  | _ -> hard_failure (Failure "improper arguments.")

(** Declare the tactic. *)
let rewrite_oracle_tac args s sk fk =
  try sk (rewrite_oracle_args args s) fk with
  | Tactics.Tactic_soft_failure e -> fk e

(*------------------------------------------------------------------*)
let () =
  T.register_general "rewrite oracle"
    ~pq_sound:false
    (LT.gentac_of_etac_arg rewrite_oracle_tac)
