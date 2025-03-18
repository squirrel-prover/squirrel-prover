type pending_proof = 
  | ProofObl of Goal.t          
  (** proof obligation *)
  | UnprovedLemma of Goal.statement * Goal.t
  (** lemma remaining to be proved *)

type prover_mode = GoalMode | ProofMode | WaitQed | AllDone

(*------------------------------------------------------------------*)
(** {2 User printing query} *)
(** User printing query *)
type print_query =
  | Pr_system    of SystemExpr.Parse.t option
  (** system printing query ([None] means current system) *)
  | Pr_any of Symbols.p_path   
  (** print query in in all kinds of symbols *)

(*------------------------------------------------------------------*)
(** {2 User search query} *)
type search_query = (* [None] means current system *)
  | Srch_term    of Typing.any_term
  | Srch_inSys   of Typing.any_term * SystemExpr.Parse.t 

(** Includes *)

type load_path = 
  | Name of string Location.located
  | Path of string Location.located

let lsymb_of_load_path = function
  | Name s
  | Path s -> s

type include_param = { th_name : load_path; 
                       params : Symbols.lsymb list }

(*------------------------------------------------------------------*)
(** Tactics *)

type bulleted_tactic =
  | Bullet of string
  | Brace of [`Open | `Close]
  | BTactic of ProverTactics.AST.t

type bulleted_tactics = bulleted_tactic list

(*------------------------------------------------------------------*)
(** Prover input *)
type input = 
  | InputDescr of Decl.declarations
  | SetOption of TConfig.p_set_param
  | Tactic of bulleted_tactics
  | Print of print_query
  | Search of search_query
  | Prof
  | Help
  | Reset
  | Goal of Goal.Parsed.t Location.located
  | Proof
  | Qed
  | Abort
  | Hint of Hint.p_hint
  | EOF
  | Include of include_param

type input_or_undo =
  | Input of input  (** Execute one input. *)
  | Undo of int     (** Undo some number of previous inputs. *)

(*---------------- Errors in proverlib -----------------------*)
(** TOMOVE Error handling in prover *)
type error = Location.t * string

exception Error of error

let error loc s = raise (Error (loc, s))

let pp_error pp_loc_err fmt (loc,s) =
  Fmt.pf fmt "%aError: %s"
    pp_loc_err loc
    s

(* Generate new unnamed goal.
   This uses an internal counter and side effects but
   that seems harmless. *)
let unnamed_goal =
  let cpt = ref 0 in
  fun () ->
    incr cpt;
    Location.mk_loc Location._dummy ("unnamed" ^ string_of_int !cpt)
