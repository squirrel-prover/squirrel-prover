(** Generic tactics *)

(** {2 Tactics} *)

(** A tactic ['a tac] is applied to a goal and non-deterministically returns
  * a list of subgoals.
  *
  * This non-deterministic computation is encoded by means of success and
  * failure continuations. The success continuation takes as argument
  * a possible result (a list of new subgoals) and a failure continuation
  * that can be called to ask for other possible successes.

  * As an example, if a tactic [tac] simply needs to change a goal
  * [j] into a list of subgoals [l], [tac j sk fk] should simply be
  * [sk l fk]. In particular, if [l] is empty, the initial will
  * be considered proved.
  *
  * When a tactic cannot produce new results, it should call its failure
  * continuation with an error explaining the failure. This is also the
  * way to go when the tactic fails to apply.
  *
  * A tactic should raise an exception only if the tactic invocation
  * is not well-formed. For instance, a typing error or a syntax error
  * should raise an exception.
  *
  * We allow tactics to not make progress and not fail. *)

type tac_error =
  | Failure of string
  | AndThen_Failure of tac_error

exception Tactic_Hard_Failure of string

val pp_tac_error : Format.formatter -> tac_error -> unit

type 'a fk = tac_error -> 'a

type ('a,'b) sk = 'a -> 'b fk -> 'b

(** A properly implemented tactic should always have its ['a]
  * parameter unconstrained. *)
type ('a,'j) tac = 'j -> ('j list,'a) sk -> 'a fk -> 'a

(** {2 Generic tactic combinators} *)

(** [orelse t1 t2] applies either [t1] or [t2]. *)
val orelse : ('a,'j) tac -> ('a,'j) tac -> ('a,'j) tac

(** [repeat t] applies [t] and applies it to the generated subgoals,
  * until [t] fails. This tactic never fails. *)
val repeat : ('a,'j) tac -> ('a,'j) tac

(** [andthen t1 t2] applies [t1] and then applies [t2] to each newly
  * created subgoal. *)
val andthen : ('a,'j) tac -> ('a,'j) tac -> ('a,'j) tac

(** n-ary variant of [orelse]. *)
val orelse_list : ('a,'j) tac list -> ('a,'j) tac

(** n-ary variant of [andthen]. *)
val andthen_list : ('a,'j) tac list -> ('a,'j) tac
