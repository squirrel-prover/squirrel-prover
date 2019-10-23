(** Main tactics of the prover *)
open Logic

type 'a fk = unit -> 'a

type ('a,'b) sk = 'a -> 'b fk -> 'b

type 'a tac =
  Judgment.t -> (Judgment.t list,'a) sk -> 'a fk -> 'a

(** Utilities *)

val remove_finished : Judgment.t list -> Judgment.t list
val simplify : Judgment.t -> Judgment.t

(** Generic tactic combinators *)

val tact_orelse : 'a tac -> 'a tac -> 'a tac
val repeat : 'a tac -> 'a tac

(** TODO this makes no sense *)
val tact_andthen :
  ('a -> ('b -> 'c -> 'd) -> 'e -> 'f) ->
  ('b -> 'g -> 'c -> 'd) -> 'g -> 'e -> 'a -> 'f

(** Basic logic-specific tactics *)

val goal_forall_intro : 'a tac
(** [goal_exists_intro judge sk fk vnu inu] introduces the existentially
    quantified variables and the goal.
    [vnu] (resp. [inu]) is a mapping from the postcondition existentially binded
    timestamp (resp. index) variables to [judge.gamma] timestamp (resp. index)
    variables. *)
val goal_exists_intro : Term.subst -> 'a tac
val goal_any_intro : 'a tac
val goal_or_intro_l : 'a tac
val goal_or_intro_r : 'a tac
val goal_and_intro : 'a tac
val goal_intro : 'a tac

val gamma_absurd : 'a tac
val constr_absurd : 'a tac
    
(** Add index constraints resulting from names equalities, modulo the TRS.
    [judge.gamma] must have been completed before calling [eq_names]. *)
val eq_names : 'a tac
val eq_timestamps : 'a tac
val eq_constants : Term.fname -> 'a tac

val apply : Term.formula -> Term.subst -> 'a tac

val euf_apply : (Term.atom -> Logic.tag -> bool) -> 'a tac
