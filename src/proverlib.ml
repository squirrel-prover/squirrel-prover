(*---------------- Errors in proverlib -----------------------*)(* {↓{ *)
(** TOMOVE Error handling in prover *)
type error = Location.t * string

exception Error of error

let error loc s = raise (Error (loc, s))

let pp_error pp_loc_err fmt (loc,s) =
  Fmt.pf fmt "%aError: %s"
    pp_loc_err loc
    s
(* }↑} *)

(* XXX This cpt has side effects : maybe keep it in the state ? 
 * Same name goal generates error ! *)
let unnamed_goal =
  let cpt = ref 0 in
  fun () ->
    incr cpt;
    Location.mk_loc Location._dummy ("unnamedgoal" ^ string_of_int !cpt)

(** {2 User printing query} *)
(** User printing query *)
type print_query = (* [None] means current system *)
  | Pr_system    of SystemExpr.Parse.t option 
  | Pr_statement of Theory.lsymb
  
(*------------------------------------------------------------------*)
(** {2 Declare Goals And Proofs} *)
type include_param = { th_name : Theory.lsymb; 
                       params : Theory.lsymb list }

(* This should move somewhere else *)
type parsed_input =
  | ParsedInputDescr of Decl.declarations
  | ParsedSetOption  of Config.p_set_param

  | ParsedTactic of [ `Bullet of string 
                    | `Brace of [`Open|`Close] 
                    | `Tactic of TacticsArgs.parser_arg Tactics.ast ] list

  | ParsedPrint   of print_query
  | ParsedUndo    of int
  | ParsedGoal    of Goal.Parsed.t Location.located
  | ParsedInclude of include_param
  | ParsedProof
  | ParsedQed
  | ParsedAbort
  | ParsedHint of Hint.p_hint
  | EOF

type pending_proof = 
  | ProofObl of Goal.t          
  (** proof obligation *)
  | UnprovedLemma of Goal.statement * Goal.t
  (** lemma remaining to be proved *)

type prover_mode = GoalMode | ProofMode | WaitQed | AllDone

(*--------------- Options are still global refs --------------------*)(* {↓{ *)
(** {2 Options}

    TODO [option_defs] is not directly related to
    this module and should be moved elsewhere, e.g. [Main] could
    deal with them through the table. *)

type option_name =
  | Oracle_for_symbol of string

type option_val =
  | Oracle_formula of Term.term

type option_def = option_name * option_val

let option_defs : option_def list ref = ref []

(*------------------------------------------------------------------*)
(** Options Management **)

exception Option_already_defined

let get_option opt_name =
  try Some (List.assoc opt_name !option_defs)
  with Not_found -> None

let add_option ((opt_name,opt_val):option_def) =
  if List.mem_assoc opt_name !option_defs then
    raise Option_already_defined
  else
    option_defs := (opt_name,opt_val) :: (!option_defs)

let get_oracle_tag_formula h =
  match get_option (Oracle_for_symbol h) with
  | Some (Oracle_formula f) -> f
  | None -> Term.mk_false
(* }↑} *)
