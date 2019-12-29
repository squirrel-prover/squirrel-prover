(** Tactics for trace properties.
  *
  * TODO All these functions are probably not useful to re-use:
  * the interface could be empty. However the documentation below
  * would be more useful if it could be seen by the user of the
  * prover. *)

open Bformula
open Formula

type tac = Sequent.t Tactics.tac

(** {2 Basic logic-specific tactics} *)

(** Reduce a goal with a disjunction conclusion into the goal
  * where the conclusion has been replace with the first disjunct. *)
val goal_or_right_1 : tac

(** Reduce a goal with a disjunction conclusion into the goal
  * where the conclusion has been replace with the second disjunct. *)
val goal_or_right_2 : tac

(** Split a conjunction conclusion,
  * creating one subgoal per conjunct. *)
val goal_and_right : tac

(** [goal_intro judge sk fk] perform one introduction, either of a forall
    quantifier or an implication. Else, it returns [fk] *)
val goal_intro : tac

(** [goal_exists_intro judge ths] introduces the existentially
    quantified variables in the conclusion of the judgment,
    using [ths] as existential witnesses. *)
val goal_exists_intro : Theory.term list -> tac

(** [congruence judge sk fk] try to close the goal using congruence, else
    calls [fk] *)
val congruence : tac

(** [assumption judge sk fk] proves the sequent using the axiom rule. *)
val assumption : tac

(** [constraints judge sk fk] proves the sequent using its trace
  * formulas. *)
val constraints : tac

(** Add index constraints resulting from names equalities, modulo the TRS.
    The judgment must have been completed before calling [eq_names]. *)
val eq_names : tac

(** Add terms constraints resulting from timestamp equalities. *)
val eq_timestamps : tac

(** {2 Advanced tactics} *)

(** [apply gp ths judge sk fk] applies the axiom [gp] with its universally
    quantified variables instantied with [ths], adding to [judge] its
    postconditions, and creating new subgoals from [judge] for the
    preconditions. *)
val apply : string -> Theory.term list -> tac

(** [tac_assert f j sk fk] generates two subgoals, one where [f] needs
  * to be proved, and the other where [f] is assumed. *)
val tac_assert : formula -> tac

(** [euf_apply f_select judge sk fk] selects an atom of the judgement according
   to [f_selct] and then try to applly euf to it. If it fails, or f_select fails
   it calls [fk]*)
val euf_apply : string -> tac

(** [collision_resistance judge sk fk] collects all equalities between hashes,
    and adds the equalities of the messages hashed with the same key. *)
val collision_resistance : tac
