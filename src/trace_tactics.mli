(** Tactics for trace properties *)

open Logic
open Bformula
open Formula

type 'a tac = ('a,Judgment.t) Tactics.tac

(** {2 Utilities} *)

val remove_finished : Judgment.t list -> Judgment.t list
val simplify : Judgment.t -> Judgment.t

(** {2 Basic logic-specific tactics} *)

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

(** Ayntactic sugar, trying to apply one of the intro. TODO inside prover ?*)
val goal_any_intro : 'a tac

(** [gamma_absurd judge sk fk] try to close the goal using congruence, else
    calls [fk] *)
val gamma_absurd : 'a tac

(** [assumption judge sk fk] try to close the goal by finding it in the 
    context. *)
val assumption : 'a tac

(** [constr_absurd judge sk fk] try to close the goal that the trace constraints
    cannot be satisfied, else calls [fk] *)
val constr_absurd : 'a tac

(** Add index constraints resulting from names equalities, modulo the TRS.
    [judge.gamma] must have been completed before calling [eq_names]. *)
val eq_names : 'a tac

(** Add terms constraints resulting from timestamp equalities. *)
val eq_timestamps : 'a tac
val eq_constants : Term.fname -> 'a tac

(** {2 Advanced tactics} *)

(** [apply gp subst judge sk fk] applies the axiom [gp] with its universally
    quantified variables instantied with [subst], adding to [judge] its
    postconditions, and creating new subgoals from [judge] for the
    preconditions. *)
val apply : formula -> Term.subst -> 'a tac

(** [tac_assert f j sk fk] generates two subgoals, one where [f] needs
  * to be proved, and the other where [f] is assumed. *)
val tac_assert : formula -> 'a tac

(** [euf_apply f_select judge sk fk] selects an atom of the judgement according
   to [f_selct] and then try to applly euf to it. If it fails, or f_select fails
   it calls [fk]*)
val euf_apply : (term_atom -> Logic.tag -> bool) -> 'a tac

(** [collision_resistance judge sk fk] collects all equalities between hash,
    and add to Gamma the equality of the messages if the hash and the key are
    identical.
*)
val collision_resistance : 'a tac

