(** Infrastructure for interactive proofs:
    proved lemmas, current lemma, current goals.
    It contains the state of the proof and the history as mutable states. *)

module L = Location
module SE = SystemExpr

module TS = LowTraceSequent

type lsymb = Theory.lsymb

(** Return the name of the goal currently being proved, if any. *)
val current_goal_name : unit -> string option

(** Current mode of the prover:
    - [GoalMode] : waiting for the next goal.
    - [ProofMode] : proof of a goal in progress.
    - [WaitQed] : finished proof, waiting for closure.
    - [AllDone] : everything is done, waiting to leave the prover.
*)
type prover_mode = GoalMode | ProofMode | WaitQed | AllDone

val current_hint_db : unit -> Hint.hint_db
val set_hint_db : Hint.hint_db -> unit


(*------------------------------------------------------------------*)
(** {2 History management} *)

type proof_state

(** Abort the current proof. *)
val abort : unit -> unit

(** Get the current prover state. *)
val get_state : prover_mode -> Symbols.table -> proof_state

(** Restore a proof state. *)
val reset_from_state : proof_state -> prover_mode * Symbols.table

(*------------------------------------------------------------------*)
(** {3 Stateful interface} *)

(** Set the proof_state to its initial state. *)
val reset : unit -> unit

(** Save the current prover state. *)
val save_state : prover_mode -> Symbols.table -> unit

(** Restore the n-th previous prover state and return the
  * corresponding prover mode. *)
val reset_state : int -> prover_mode * Symbols.table

(** Push a new empty proof state history in the stack, to enter an `include` *)
val push_pt_history : unit -> unit

(** Pop a proof state history from the stack, to exit an `include` *)
val pop_pt_history : unit -> unit

(** Pop all proof state history from the stack, when an `include` fails *)
val pop_all_pt_history : unit -> unit

(** Reset the state to the top of the proof state history (leaving the
    history unchanged). *)
val reset_to_pt_history_head : unit -> prover_mode * Symbols.table

(** Option management **)
type option_name =
  | Oracle_for_symbol of string

type option_val =
  | Oracle_formula of Term.message

type option_def = option_name * option_val

exception Option_already_defined

val get_option : option_name -> option_val option

val add_option : option_def -> unit

(*------------------------------------------------------------------*)
(** {2 Tactics syntax trees} *)
(** Prover tactics, and tables for storing them. *)

(* TODO module AST : Tactics.AST_sig
   with type arg = tac_arg and type judgment = Sequent.t *)


(* Define formats of help informations for tactics *)
type tactic_groups =
  | Logical   (* A logic tactic is a tactic that relies on the sequence calculus
                 logical properties. *)
  | Structural (* A structural tactic relies on properties inherent to protocol,
                  on equality between messages, behaviour of if _ then _ else _,
                  action dependencies... *)
  | Cryptographic (* Cryptographic assumptions rely on ... a cryptographic assumption ! *)


(* The record for a detailed help tactic. *)
type tactic_help = { general_help : string;
                     detailed_help : string;
                     usages_sorts : TacticsArgs.esort list;
                     tactic_group : tactic_groups}


(** Registry for tactics on some kind of judgment *)
module ProverTactics : sig
  type judgment = Goal.t
  type tac = judgment Tactics.tac

  (* Allows to register a general tactic. Used when the arguments of the tactic
     are complex. *)

  val register_general :
    string -> tactic_help:tactic_help ->
    (TacticsArgs.parser_arg list -> tac) -> unit

  (* Register a macro, built using the AST. *)
  val register_macro :
    string -> ?modifiers:string list -> tactic_help:tactic_help ->
    TacticsArgs.parser_arg Tactics.ast -> unit

(* The remaining functions allows to easily register a tactic, without having to
   manage type conversions, or the tail recursvity. It is simply required to
   give a function over judgments, expecting some arguments of the given
   sort. *)
  val register : string -> tactic_help:tactic_help ->
    (judgment -> judgment list) -> unit

  val register_typed :
    string ->  general_help:string ->  detailed_help:string ->
    tactic_group:tactic_groups ->
    ?usages_sorts : TacticsArgs.esort list ->
    ('a TacticsArgs.arg -> judgment -> judgment list) ->
    'a TacticsArgs.sort  -> unit

  val get : string -> TacticsArgs.parser_arg list -> tac
  val pp : bool -> Format.formatter -> lsymb -> unit

  (* Print all tactics with their help. Do not print tactics without help
     string. *)
  val pps : Format.formatter -> unit -> unit
  val pp_list : Format.formatter -> unit -> unit
end

val pp_ast : Format.formatter -> TacticsArgs.parser_arg Tactics.ast -> unit

(*------------------------------------------------------------------*)
(** {2 Misc} *)

(** Get proved or assumed statement. *)
val get_assumption       : lsymb -> Goal.statement
val get_reach_assumption : lsymb -> Goal.reach_statement
val get_equiv_assumption : lsymb -> Goal.equiv_statement

val is_assumption       : string -> bool
val is_reach_assumption : string -> bool
val is_equiv_assumption : string -> bool

(*------------------------------------------------------------------*)
(** {2 Utilities for parsing} *)

exception ParseError of string

type parsed_input =
  | ParsedInputDescr of Decl.declarations
  | ParsedSetOption  of Config.p_set_param
  | ParsedTactic     of TacticsArgs.parser_arg Tactics.ast
  | ParsedUndo       of int
  | ParsedGoal       of Goal.Parsed.t Location.located
  | ParsedInclude    of lsymb
  | ParsedProof
  | ParsedQed
  | ParsedAbort
  | ParsedHint       of Hint.p_hint
  | EOF

(** Declare a new goal to the current goals, and returns it *)
val declare_new_goal :
  Symbols.table ->
  Hint.hint_db ->
  Goal.Parsed.t Location.located ->
  string * Goal.t

(** From the name of the function, returns the corresponding formula. If no tag
   formula was defined, returns False. *)
val get_oracle_tag_formula : string -> Term.message

val pp_goal : Format.formatter -> unit -> unit

val is_proof_completed : unit -> bool

(** Complete the proofs, resetting the current goal to None. *)
val complete_proof : unit -> unit

(** [eval_tactic utac] applies the tactic [utac].
    Return [true] if there are no subgoals remaining. *)
val eval_tactic : TacticsArgs.parser_arg Tactics.ast -> bool

(** Initialize the prover state try to prove the first of the unproved goal. *)
val start_proof : unit -> string option

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type decl_error_i =
  | BadEquivForm
  | InvalidAbsType
  | InvalidCtySpace of string list
  | DuplicateCty of string

  | SystemError     of System.system_error
  | SystemExprError of SE.system_expr_err

type dkind = KDecl | KGoal

type decl_error =  L.t * dkind * decl_error_i

exception Decl_error of decl_error

val pp_decl_error :
  (Format.formatter -> L.t -> unit) ->
  Format.formatter -> decl_error -> unit

(*------------------------------------------------------------------*)
(** {2 Declaration processing} *)

(** Process a declaration. *)
val declare : 
  Symbols.table -> Hint.hint_db -> Decl.declaration  -> Symbols.table

(** Process a list of declaration. *)
val declare_list : 
  Symbols.table -> Hint.hint_db -> Decl.declarations -> Symbols.table

(*------------------------------------------------------------------*)
val add_hint_rewrite : lsymb -> Hint.hint_db -> Hint.hint_db
