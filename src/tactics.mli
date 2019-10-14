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
val goal_exists_intro : Term.subst -> 'a tac
val goal_any_intro : 'a tac
val goal_or_intro_l : 'a tac
val goal_or_intro_r : 'a tac
val goal_and_intro : 'a tac
val goal_intro : 'a tac

val gamma_absurd : 'a tac
val constr_absurd : 'a tac

val eq_names : 'a tac
val eq_timestamps : 'a tac
val eq_constants : Term.fname -> 'a tac

val apply : Term.formula -> Term.subst -> 'a tac

val euf_apply : (Term.atom -> Logic.tag -> bool) -> 'a tac
