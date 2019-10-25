(** Main tactics of the prover *)
open Logic

(*
type tac_error =
    | Failure of string

val pp_tac_error

type 'a fk = tac_error -> 'a
*)

type 'a fk = unit -> 'a

type ('a,'b) sk = 'a -> 'b fk -> 'b


(** A tactic ['a tac] is applied to a goal with both a success continuation [sk]
    and a failure continuation [fk].
    A tactic, in case of success, returns a set of subgoals. If the tactic
    closed the focused goal, it returns the empty list.

    The success continuation takes as argument the new set of subgoals and
    a failure continuation.

    As an example, the function [tac] given by [tac judge sk fk] should return
    [sk new_judges fk] in case of success and [fk ()] in case of failure.

    We allow tactics to not make progress and not fail.

    A tactic should raise an exception only if the tactic is not well-formed
    or applicable. For instance, a typing error or a syntax error should raise
    an exception.

    Tactic failures should pass to the failure continuation an error
    under the type [tac_error]. [tac_error] can be extended for the need of
    each tactic, [pp_tac_error] should then be extended accordingly.

    Tactic combinators, may choose how to pass tactic errors, depending


*)
type 'a tac =
  Judgment.t -> (Judgment.t list,'a) sk -> 'a fk -> 'a

(** Utilities *)

val remove_finished : Judgment.t list -> Judgment.t list
val simplify : Judgment.t -> Judgment.t

(** Generic tactic combinators *)

(** [tact_orelse t1 t2] applies [t1] with [t2] as failure continuation. *)
val tact_orelse : 'a tac -> 'a tac -> 'a tac

(** [repeat t] applies [t] until either [t] fails or a fix point is reached. *)
val repeat : 'a tac -> 'a tac

(** [tact_andthen t1 t2] applies [t1], creating subgoals [gs] and try to apply
    [t2] to each subgoal in [gs]. It succeed only if all applications of [t2]
    succeeds. *)
val tact_andthen :
  'a tac ->
  Judgment.t list tac ->
  'a tac


(** Basic logic-specific tactics *)

(** TODO: les intro raise des hard failure au lieu de soft *)

(** [goal_or_intro_l judge sk fk] returns the left side of the goal if it is
    a disjunction. Else it calls [fk] *)
val goal_or_intro_l : 'a tac
(** [goal_or_intro_r judge sk fk] returns the right side of the goal if it is
    a disjunction. Else it calls [fk] *)
val goal_or_intro_r : 'a tac
(** [goal_and_intro judge sk fk] returns the right side of the goal if it is
    a conjonction. Else it calls [fk] *)
val goal_and_intro : 'a tac

(** [goal_intro judge sk fk] introduce a fact if the goal is one. Else it calls
    [fk] *)
val goal_intro : 'a tac

(** [goal_forall_intro judge sk fk] introduces the universally
    quantified variables and the goal. *)
val goal_forall_intro : 'a tac
(** [goal_exists_intro judge sk fk vnu inu] introduces the existentially
    quantified variables and the goal.
    [vnu] (resp. [inu]) is a mapping from the postcondition existentially binded
    timestamp (resp. index) variables to [judge.gamma] timestamp (resp. index)
    variables. *)
val goal_exists_intro : Term.subst -> 'a tac

(** should not exist, syntactic sugar based on orelse *)
val goal_any_intro : 'a tac

(** [gamma_absurd judge sk fk] try to close the goal using congruence, else
    calls [fk] *)
val gamma_absurd : 'a tac
(** [constr_absurd judge sk fk] try to close the goal that the trace constraints
    cannot be satisfied, else calls [fk] *)
val constr_absurd : 'a tac

(** Add index constraints resulting from names equalities, modulo the TRS.
    [judge.gamma] must have been completed before calling [eq_names]. *)
val eq_names : 'a tac
(** Add terms constraints resulting from timestamp equalities. *)
val eq_timestamps : 'a tac
val eq_constants : Term.fname -> 'a tac

(** [apply gp subst judge sk fk] applies the axiom [gp] with its universally
    quantified variables instantied with [subst], adding to [judge] its
    postconditions, and creating new subgoals from [judge] for the
    preconditions. *)
val apply : Term.formula -> Term.subst -> 'a tac

(** [euf_apply f_select judge sk fk] selects an atom of the judgement according
   to [f_selct] and then try to applly euf to it. If it fails, or f_select fails
   it calls [fk]*)
val euf_apply : (Term.atom -> Logic.tag -> bool) -> 'a tac
