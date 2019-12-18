(** Tactics for trace properties.
  *
  * TODO All these functions are probably not useful to re-use:
  * the interface could be empty. However the documentation below
  * would be more useful if it could be seen by the user of the
  * prover. *)

open Sequent
open Bformula
open Formula

type tac = sequent Tactics.tac

(** {2 Basic logic-specific tactics} *)

(** [goal_or_intro_l judge sk fk] returns the left side of the goal if it is
    a disjunction. Else it calls [fk] *)
val goal_or_intro_l : tac
(** [goal_or_intro_r judge sk fk] returns the right side of the goal if it is
    a disjunction. Else it calls [fk] *)
val goal_or_intro_r : tac
(** [goal_and_intro judge sk fk] returns the right side of the goal if it is
    a conjonction. Else it calls [fk] *)
val goal_and_intro : tac

(** [goal_intro judge sk fk] perform one introduction, either of a forall
    quantifier or an implication. Else, it returns [fk] *)
val goal_intro : tac

(** [goal_exists_intro judge sk fk nu] introduces the existentially
    quantified variables in the conclusion of the judgment.
    The substitution [nu] is a mapping from the existentially bound
    variables to terms over the current variables of the judgment. *)
val goal_exists_intro : Term.subst -> tac

(** [congruence judge sk fk] try to close the goal using congruence, else
    calls [fk] *)
val congruence : tac

(** [assumption judge sk fk] try to close the goal by finding it in the
    context. *)
val assumption : tac

(** [constr_absurd judge sk fk] try to close the goal that the trace constraints
    cannot be satisfied, else calls [fk] *)
val constr_absurd : tac

(** Add index constraints resulting from names equalities, modulo the TRS.
    [judge.gamma] must have been completed before calling [eq_names]. *)
val eq_names : tac

(** Add terms constraints resulting from timestamp equalities. *)
val eq_timestamps : tac
val eq_constants : Term.fname -> tac

(** {2 Advanced tactics} *)

(** [apply gp subst judge sk fk] applies the axiom [gp] with its universally
    quantified variables instantied with [subst], adding to [judge] its
    postconditions, and creating new subgoals from [judge] for the
    preconditions. *)
val apply : formula -> Term.subst -> tac

(** [tac_assert f j sk fk] generates two subgoals, one where [f] needs
  * to be proved, and the other where [f] is assumed. *)
val tac_assert : formula -> tac

(** [euf_apply f_select judge sk fk] selects an atom of the judgement according
   to [f_selct] and then try to applly euf to it. If it fails, or f_select fails
   it calls [fk]*)
val euf_apply : string -> tac

(** [collision_resistance judge sk fk] collects all equalities between hash,
    and add to Gamma the equality of the messages if the hash and the key are
    identical.
*)
val collision_resistance : tac
