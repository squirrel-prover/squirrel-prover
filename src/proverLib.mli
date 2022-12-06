(** Current mode of the prover:
    - [GoalMode] : waiting for the next goal.
    - [ProofMode] : proof of a goal in progress.
    - [WaitQed] : finished proof, waiting for closure.
    - [AllDone] : everything is done, waiting to leave the prover.
*)
type prover_mode = GoalMode | ProofMode | WaitQed | AllDone

type pending_proof = 
  | ProofObl of Goal.t          
  (** proof obligation *)
  | UnprovedLemma of Goal.statement * Goal.t
  (** lemma remaining to be proved *)

(** Option management **)
type option_name =
  | Oracle_for_symbol of string

type option_val =
  | Oracle_formula of Term.term

type option_def = option_name * option_val

exception Option_already_defined

val get_option : option_name -> option_val option

val add_option : option_def -> unit

(** From the name of the function, returns the corresponding formula. If no tag
   formula was defined, returns False. *)
val get_oracle_tag_formula : string -> Term.term

val option_defs : option_def list ref

(*------------------------------------------------------------------*)
(** {2 User printing query} *)

(** User printing query *)
type print_query =
  | Pr_system    of SystemExpr.Parse.t option (* [None] means current system *)
  | Pr_statement of Theory.lsymb

(*------------------------------------------------------------------*)
(** Error handling *)

type error = Location.t * string

exception Error of error

val error : Location.t -> string -> 'a

val pp_error :
  (Format.formatter -> Location.t -> unit) -> 
  Format.formatter -> error -> unit


(* TOMOVE in prover.ml cpt in state TODO !*)
val unnamed_goal : unit -> Theory.lsymb

(*------------------------------------------------------------------*)
(** {2 Utilities for parsing} *)

type include_param = { th_name : Theory.lsymb; params : Theory.lsymb list }

type bulleted_tactic =
  | Bullet of string
  | Brace of [`Open | `Close]
  | Tactic of TacticsArgs.parser_arg Tactics.ast

type bulleted_tactics = bulleted_tactic list

(*------------------------------------------------------------------*)
type parsed_input =
  | ParsedInputDescr of Decl.declarations
  | ParsedSetOption  of Config.p_set_param

  | ParsedTactic of bulleted_tactics

  | ParsedPrint   of print_query
  | ParsedUndo    of int
  | ParsedGoal    of Goal.Parsed.t Location.located
  | ParsedInclude of include_param
  | ParsedProof
  | ParsedQed
  | ParsedAbort
  | ParsedHint of Hint.p_hint
  | EOF

