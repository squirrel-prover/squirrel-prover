(** Generic tactics *)

module L = Location

type lsymb = string L.located

(*------------------------------------------------------------------*)
(** {2 Tactics} *)

(** A tactic ['a tac] is a non-deterministic computation
    transforming a goal of type ['a] into a list of subgoals.
    
    This non-deterministic computation is encoded by means of success and
    failure continuations. The success continuation takes as argument
    a possible result (a list of new subgoals) and a failure continuation
    that can be called to ask for other possible successes.
   
    As an example, if a tactic [tac] simply needs to change a goal
    [j] into a list of subgoals [l], [tac j sk fk] should simply be
    [sk l fk]. In particular, if [l] is empty, the initial goal will
    be considered proved.
   
    When a tactic cannot produce new results, it should call its failure
    continuation with an error explaining the failure. This is also the
    way to go when the tactic fails to apply.
   
    A tactic should raise an exception only if the tactic invocation
    is not well-formed. For instance, a typing error or a syntax error
    should raise an exception.
   
    We allow tactics to not make progress and not fail. *)

(*------------------------------------------------------------------*)
(** Errors returned when the axiom syntactic side-conditions do not hold. *)
type ssc_error_c =
  | E_message
  | E_elem
  | E_indirect of
      Symbols.action *
      [`Cond | `Output | `Update of Symbols.macro | `Global of Symbols.macro]

type ssc_error = Term.term * ssc_error_c

val pp_ssc_error  : Format.formatter -> ssc_error      -> unit
val pp_ssc_errors : Format.formatter -> ssc_error list -> unit

(*------------------------------------------------------------------*)
(** The multiple types of tactics error. Specific ones are defined so that they
    may be caught for unit testing. *)
type tac_error_i =
  | More
  | Failure of string
  | CannotConvert
  | NotEqualArguments
  | Bad_SSC
  | BadSSCDetailed of ssc_error list
  | NoSSC
  | NoAssumpSystem of string
  | Rewrite_equiv_system_mismatch
  | Underspecified_system
  | NotDepends of string * string
  | NotDDHContext
  | SEncNoRandom
  | SEncSharedRandom
  | SEncRandomNotFresh
  | NameNotUnderEnc
  | NoRefl
  | NoReflMacroVar
  | TacTimeout
  | DidNotFail
  | FailWithUnexpected of tac_error_i
  | GoalBadShape of string
  | GoalNotPQSound
  | TacticNotPQSound
  | CongrFail
  | GoalNotClosed
  | NothingToIntroduce
  | NothingToRewrite
  | BadRewriteRule
  | MustHappen of Term.term
  | NotHypothesis
  | ApplyMatchFailure of (Term.terms * Term.match_infos) option
  | ApplyBadInst
  | NoCollision
  | HypAlreadyExists of string
  | HypUnknown of string
  | InvalidVarName
  | PatNumError of int * int    (* given, need *)
  | CannotInferPats

type tac_error = L.t option * tac_error_i

(** Tactics should raise this exception if they are ill-formed. *)
exception Tactic_soft_failure of tac_error

(** This tactic should be raised by the evaluation of a tactic, based on the
    tac_error returned by its failure. *)
exception Tactic_hard_failure of tac_error

val pp_tac_error_i : Format.formatter -> tac_error_i -> unit

(** Purely abstract type "returned" by continuations and tactics. *)
type a

type fk = tac_error -> a

type 'a sk = 'a -> fk -> a

(** A ['a tac] is a tactic working on judgments of type ['a],
    which can be seen as a non-deterministic computation
    taking a judgment as input and returning a list of judgments.
    This computation is performed in continuation-passing style,
    the possible results are passed to the [sk] continuation
    successively, and [fk] is called when no (more) result is available. *)
type 'a tac = 'a -> 'a list sk -> fk -> a

(** Run a tactic and return its first result.
    The tactic must not fail. *)
val run : 'a tac -> 'a -> 'a list

(*------------------------------------------------------------------*)
(** {2 Generic tactics and tactic combinators} *)

val id : 'a tac

(** [orelse t1 t2] applies either [t1] or [t2]. *)
val orelse : 'a tac -> 'a tac -> 'a tac

(** [repeat t] applies [t] and applies it to the generated subgoals,
  * until [t] fails. This tactic never fails. *)
val repeat : ?cut:bool -> 'a tac -> 'a tac

(** [andthen t1 t2] applies [t1] and then applies [t2] to each newly
  * created subgoal. *)
val andthen : ?cut:bool -> 'a tac -> 'a tac -> 'a tac

(** n-ary variant of [orelse]. *)
val orelse_list : 'a tac list -> 'a tac

(** n-ary variant of [andthen]. *)
val andthen_list : ?cut:bool -> 'a tac list -> 'a tac

val try_tac : 'a tac -> 'a tac

(*------------------------------------------------------------------*)
(** {2 Generic tactic syntax trees} *)

type selector = int list

(** AST for tactics, with abstract atomic leaves.
    Modifiers have no specific semantics and are simply propagated
    to impact the evaluation of atoms. *)
type 'a ast =
  | Abstract   : lsymb * 'a list -> 'a ast
  | AndThen    : 'a ast list -> 'a ast
  | AndThenSel : 'a ast * (selector * 'a ast) list -> 'a ast
  | OrElse     : 'a ast list -> 'a ast
  | Try        : 'a ast -> 'a ast
  | Repeat     : 'a ast -> 'a ast
  | Ident      : 'a ast
  | Modifier   : string * 'a ast -> 'a ast
  | CheckFail  : string * 'a ast -> 'a ast
  | By         : 'a ast * L.t -> 'a ast
  | Time       : 'a ast -> 'a ast

(** Operations required to evaluate any [arg ast] as [judgment tac]:
    we must be able to display arguments and evaluate abstract leaves. *)
module type S = sig
  type arg
  type judgment
  val pp_arg : Format.formatter -> arg -> unit
  val eval_abstract :
    post_quantum:bool -> modifiers:string list ->
    lsymb -> arg list -> judgment tac
end

module type AST_sig = sig

  type arg
  type judgment
  type t = arg ast

  (** [eval post_quantum modifiers ast] evaluates an AST as a tactic,
      given a [post_quantum] flag and a list of modifiers.
      TODO ideally, drop PQ flag as this module should be Squirrel-agnostic *)
  val eval : post_quantum:bool -> modifiers:string list -> t -> judgment tac

  (* TODO document; this is the only place where hard/soft failures matter
     so it may be beneficial to move this to ProverTactics *)
  val eval_judgment : post_quantum:bool -> t -> judgment -> judgment list

  val pp : Format.formatter -> t -> unit

end

module AST (M:S) : AST_sig
  with type arg = M.arg
  with type judgment = M.judgment

(*------------------------------------------------------------------*)
(** {2 Utilities} *)

(** Raise a soft failure. *)
val soft_failure : ?loc:Location.t -> tac_error_i -> 'a

(** Raise a hard failure. *)
val hard_failure : ?loc:Location.t -> tac_error_i -> 'a
