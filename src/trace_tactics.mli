(** Tactics for trace properties.
  *
  * TODO All these functions are probably not useful to re-use:
  * the interface could be empty. However the documentation below
  * would be more useful if it could be seen by the user of the
  * prover. *)

open Logic
open Bformula
open Formula

type tac = Judgment.t Tactics.tac

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

(** [goal_intro judge sk fk] introduce a fact if the goal is one. Else it calls
    [fk] *)
val goal_intro : tac

(** [goal_forall_intro judge sk fk] introduces the universally
    quantified variables and the goal. *)
val goal_forall_intro : tac
(** [goal_exists_intro judge sk fk vnu inu] introduces the existentially
    quantified variables and the goal.
    [vnu] (resp. [inu]) is a mapping from the postcondition existentially binded
    timestamp (resp. index) variables to [judge.gamma] timestamp (resp. index)
    variables. *)
val goal_exists_intro : Term.subst -> tac

(** [gamma_absurd judge sk fk] try to close the goal using congruence, else
    calls [fk] *)
val gamma_absurd : tac

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
val euf_apply : (term_atom -> Logic.tag -> bool) -> tac

(** [collision_resistance judge sk fk] collects all equalities between hash,
    and add to Gamma the equality of the messages if the hash and the key are
    identical.
*)
val collision_resistance : tac
