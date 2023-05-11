open Squirrelprover
include Squirrelcore

(* Needed to register the tactics *)
include Squirreltactics

type state = {ps: Prover.state; output: string}

type stack = state list

let prover_state : Prover.state ref = ref (Prover.init ())

let firstOutput = "Prover initial state : Ready to go !"

let prover_stack : (state list) ref = ref [{ps= !prover_state;
output=firstOutput}]

let init () =
  prover_state := Prover.init ();
  prover_stack := [{ps= !prover_state; output=firstOutput}]

let push (s:state) : stack =
  let h' = s::(!prover_stack) in
  prover_stack := h';
  prover_state := s.ps;
  h'

exception Empty
exception TryToPopInit
let pop : stack * state =
  match !prover_stack with
  | [] -> raise Empty
  | s::h -> prover_stack := h;
            prover_state := s.ps;
            (h,s)

let rec popn' (i:int) (h:stack) (poped:state list) : stack * state list =
  if i = 0 then (h,poped) else
  match h with
  | [] -> raise Empty
  | [_] -> raise TryToPopInit (* should not try to pop initial state *)
  | s::h' -> popn' (i-1) h' (s::poped)

let popn (i:int) : stack * state list = 
  let h',poped = popn' i !prover_stack [] in
  prover_stack := h';
  prover_state := (List.hd h').ps; (*should always have initial state*)
  (h',poped)

let show () : string =
  let st = List.hd !prover_stack in
  st.output

let shown (i:int) : string =
  let st = List.nth !prover_stack i in
  st.output

let get_formatter = 
  Printer.get_std ()

let print_goal () = 
  match Prover.get_mode !prover_state with
  | ProverLib.ProofMode -> 
      Printer.prthtml `Goal "%a" (Prover.pp_goal !prover_state) ()
  | _ -> 
      Printer.prthtml `Goal "Nothing to show…"

let get_goal_print () : string = 
    print_goal (); (* will printout the current goal *)
    Format.flush_str_formatter ()

let pp_toplevel_error
    (fmt : Format.formatter)
    (e : exn) : unit
  =

  let file = Driver.file_from_stdin () in
  let pp_loc_error     = Driver.pp_loc_error     file in
  let pp_loc_error_opt = Driver.pp_loc_error_opt file in

  match e with
  | ProverLib.Error e ->
    ProverLib.pp_error pp_loc_error fmt e

  | Command.Cmd_error e ->
    Command.pp_cmd_error fmt e

  | Process.Error e ->
    (Process.pp_error pp_loc_error) fmt e

  | ProcessDecl.Error e ->
    (ProcessDecl.pp_error pp_loc_error) fmt e

  | Theory.Conv e ->
    (Theory.pp_error pp_loc_error) fmt e

  | Symbols.Error e ->
    (Symbols.pp_error pp_loc_error) fmt e

  | System.Error e ->
    Format.fprintf fmt "System error: %a" System.pp_error e

  | SystemExpr.Error e ->
    Format.fprintf fmt "System error: %a" SystemExpr.pp_error e

  | Tactics.Tactic_soft_failure (l,e) ->
    Fmt.pf fmt "%aTactic failed: %a"
      pp_loc_error_opt l
      Tactics.pp_tac_error_i e

  | Tactics.Tactic_hard_failure (l,e) ->
    Fmt.pf fmt "%aTactic ill-formed or unapplicable: %a"
      pp_loc_error_opt l
      Tactics.pp_tac_error_i e

  | e  ->
    Fmt.pf fmt "Anomaly, please report: %s" (Printexc.to_string e)
    
(* will return boolean that is true if every thing is ok and output *)
let exec_sentence ?(check=`Check) s : bool * string = 
  try
    prover_state := Prover.exec_all ~check !prover_state s;
    let info = Format.flush_str_formatter () in
    prover_stack := 
      push {ps= !prover_state; output= get_goal_print ()};
    (true,info)
  with e -> 
    Printer.prthtml `Error "Exec failed: %a"
      pp_toplevel_error e;
    false,Format.flush_str_formatter () (* will print the exception info *)

let exec_command ?(check=`Check) s : string = 
  try
    let _ = Prover.exec_command ~check s !prover_state in
    let info = Format.flush_str_formatter () in
    info
  with e -> 
    Printer.prthtml `Error "Run failed: %a"
      pp_toplevel_error e;
    raise e

let visualisation () : string =
 try begin 
   match Prover.get_first_subgoal !prover_state with
   | Trace j ->
         Format.asprintf "%a"
           Squirrelhtml.Visualisation.pp j
   | _ | exception _ -> 
       "{\"error\": \"Nothing to visualize\"}"
   end
  with _ -> 
    "{\"error\": \"Error for visualization.pp\"}"

let _ =
  Printer.init Printer.Html
