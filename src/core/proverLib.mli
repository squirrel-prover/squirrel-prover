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

(*------------------------------------------------------------------*)
(** {2 Printing infos} *)

(** User printing query *)
type print_query =
  | Pr_system    of SystemExpr.Parse.t option (* [None] means current system *)
  | Pr_any of Theory.lsymb (* print any lemma, function, name or macro
                              with given lsymb *)

(** User search query *)
type search_query =
  | Srch_term    of Theory.any_term
  | Srch_inSys   of Theory.any_term * SystemExpr.Parse.t 

(*------------------------------------------------------------------*)
(** Error handling *)

type error = Location.t * string

exception Error of error

val error : Location.t -> string -> 'a

val pp_error :
  (Format.formatter -> Location.t -> unit) -> 
  Format.formatter -> error -> unit

val unnamed_goal : unit -> Theory.lsymb

(*------------------------------------------------------------------*)
(** {2 Utilities for parsing} *)

type load_path = 
  | Name of string Location.located
  | Path of string Location.located

val lsymb_of_load_path : load_path -> Theory.lsymb

type include_param = { th_name : load_path; params : Theory.lsymb list }

type bulleted_tactic =
  | Bullet of string
  | Brace of [`Open | `Close]
  | BTactic of ProverTactics.AST.t

type bulleted_tactics = bulleted_tactic list

type input = 
  | InputDescr of Decl.declarations
  | SetOption  of Config.p_set_param
  | Tactic of bulleted_tactics
  | Print   of print_query
  | Search of search_query
  | Prof
  | Help
  | Reset
  | Goal    of Goal.Parsed.t Location.located
  | Proof
  | Qed
  | Abort
  | Hint of Hint.p_hint
  | EOF
  | Include of include_param

type input_or_undo =
  | Input of input  (** Execute one input. *)
  | Undo of int     (** Undo some number of previous inputs. *)