(** Infrastructure for interactive proofs:
    proved lemmas, current lemma, current goals.
    It contains the state of the proof and the history as mutable states. *)

module L = Location

type lsymb = Theory.lsymb

open Term

module Goal : sig
  type t = Trace of TraceSequent.t | Equiv of EquivSequent.t
  val pp : Format.formatter -> t -> unit
  val pp_init : Format.formatter -> t -> unit
  val get_env : t -> Vars.env
end

(** A goal of the prover is simply a name and a formula *)
type named_goal = string * Goal.t

(** [current_goal] returns the current (sub)goal of the prover,
  * if any. *)
val current_goal : unit -> named_goal option

(** Current mode of the prover:
    - [GoalMode] : waiting for the next goal.
    - [ProofMode] : proof of a goal in progress.
    - [WaitQed] : finished proof, waiting for closure.
    - [AllDone] : everything is done, waiting to leave the prover.
*)
type prover_mode = GoalMode | ProofMode | WaitQed | AllDone


(*------------------------------------------------------------------*)
(** {2 Type of parsed new goal } *)

type p_goal_name = P_unknown | P_named of lsymb


type p_equiv = Theory.term list 

type p_equiv_form = 
  | PEquiv of p_equiv
  | PReach of Theory.formula
  | PImpl  of p_equiv_form * p_equiv_form

type p_goal =
  | P_trace_goal of SystemExpr.p_system_expr * Theory.formula

  | P_equiv_goal of Theory.bnds * p_equiv_form L.located

  | P_equiv_goal_process of SystemExpr.p_single_system * 
                            SystemExpr.p_single_system

(** Goal mode input types:
    - [Gm_goal f] : declare a new goal f.
    - [Gm_proof]  : start a proof. *)
type gm_input_i =
  | Gm_goal of p_goal_name * p_goal
  | Gm_proof

type gm_input = gm_input_i L.located


(*------------------------------------------------------------------*)
(** {2 History management.} *)

type proof_state

(** Abort the current proof. *)
val abort : unit -> unit

(** Set the proof_state to its initial state. *)
val reset : unit -> unit

(** Save the current prover state. The prover mode is the only external
    information required. *)
val save_state : prover_mode -> Symbols.table -> unit

(** Restore the n-th previous prover state and return the
  * corresponding prover mode. *)
val reset_state : int -> prover_mode * Symbols.table

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
module type Tactics_sig = sig
  type judgment
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

module TraceTactics : Tactics_sig with type judgment = TraceSequent.t
module EquivTactics : Tactics_sig with type judgment = Goal.t

(*------------------------------------------------------------------*)
(** {2 Utilities for parsing} *)

exception ParseError of string

val get_goal_formula : lsymb -> message * SystemExpr.system_expr

val is_goal_formula : lsymb -> bool

(** Produces a trace goal from a parsed formula,
  * for reasoning on the traces of the given system. *)
val make_trace_goal :
  system:SystemExpr.system_expr -> table:Symbols.table ->
  Theory.formula -> Goal.t

(** Produces an equivalence goal from a sequence of parsed bi-terms. *)
val make_equiv_goal :
  table:Symbols.table -> System.system_name -> Theory.bnds ->
  p_equiv_form L.located ->
  Goal.t

(** Produces an equivalence goal based on the process and the two
    system expressions. *)
val make_equiv_goal_process :
  table:Symbols.table ->
  SystemExpr.single_system -> SystemExpr.single_system ->
  Goal.t

type parsed_input =
  | ParsedInputDescr of Decl.declarations
  | ParsedQed
  | ParsedAbort
  | ParsedSetOption of Config.p_set_param
  | ParsedTactic of TacticsArgs.parser_arg Tactics.ast
  | ParsedUndo of int
  | ParsedGoal of gm_input
  | EOF

(** Declare a new goal to the current goals, and returns it *)
val declare_new_goal :
  Symbols.table ->
  L.t -> p_goal_name -> p_goal ->
  named_goal

(** Store a proved goal, allowing to apply it. *)
val add_proved_goal : named_goal -> unit

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
  | SystemExprError of SystemExpr.system_expr_err

type dkind = KDecl | KGoal

type decl_error =  L.t * dkind * decl_error_i

exception Decl_error of decl_error

val pp_decl_error :
  (Format.formatter -> L.t -> unit) ->
  Format.formatter -> decl_error -> unit

(*------------------------------------------------------------------*)
(** {2 Declaration processing} *)

(** Process a declaration. *)
val declare      : Symbols.table -> Decl.declaration  -> Symbols.table

(** Process a list of declaration. *)
val declare_list : Symbols.table -> Decl.declarations -> Symbols.table
