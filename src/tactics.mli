(** Generic tactics *)

(** {2 Tactics} *)

(** A tactic ['a tac] is a non-deterministic computation
  * transforming a goal of type ['a] into a list of subgoals.
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
  | NotEqualArguments

exception Tactic_Hard_Failure of tac_error

exception Tactic_Soft_Failure of tac_error

val pp_tac_error : Format.formatter -> tac_error -> unit

(** Purely abstract type "returned" by continuations and tactics *)
type a

type fk = tac_error -> a

type 'a sk = 'a -> fk -> a

(** A properly implemented tactic should always have its ['a]
  * parameter unconstrained. *)
type 'a tac = 'a -> 'a list sk -> fk -> a

(** {2 Generic tactics and tactic combinators} *)

val id : 'a tac

(** [orelse t1 t2] applies either [t1] or [t2]. *)
val orelse : 'a tac -> 'a tac -> 'a tac

(** [repeat t] applies [t] and applies it to the generated subgoals,
  * until [t] fails. This tactic never fails. *)
val repeat : 'a tac -> 'a tac

(** [andthen t1 t2] applies [t1] and then applies [t2] to each newly
  * created subgoal. *)
val andthen : 'a tac -> 'a tac -> 'a tac

(** n-ary variant of [orelse]. *)
val orelse_list : 'a tac list -> 'a tac

(** n-ary variant of [andthen]. *)
val andthen_list : 'a tac list -> 'a tac

val try_tac : 'a tac -> 'a tac

(** {2 Generic tactic syntax trees} *)

module type S = sig

  type arg
  val pp_arg : Format.formatter -> arg -> unit

  type judgment

  val eval_abstract : string -> arg list -> judgment tac
  val pp_abstract : pp_args:(Format.formatter -> arg list -> unit) ->
    string -> arg list -> Format.formatter -> unit

end

module type AST_sig = sig

  type arg
  type judgment

  (** AST for tactics, with abstract leaves corresponding to prover-specific
    * tactics, with prover-specific arguments. Modifiers have no internal
    * semantics: they are printed, but ignored during evaluation -- they
    * can only be used for cheap tricks now, but may be used to guide tactic
    * evaluation in richer ways in the future. *)
  type t =
    | Abstract of string * arg list
    | AndThen : t list -> t
    | OrElse : t list -> t
    | Try : t -> t
    | Repeat : t -> t
    | Ident : t
    | Modifier : string * t -> t

  val eval : t -> judgment tac

  val pp : Format.formatter -> t -> unit

end

module AST (M:S) : AST_sig
  with type arg = M.arg
  with type judgment = M.judgment
