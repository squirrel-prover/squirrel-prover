(* A Prover driver with history and with web formatted output
 *
 * TODO :
 * - a start for client-server squirrel on browser
 *)

include Squirrelcore
include Squirrelprover

(* Needed to register the tactics *)
include Squirreltactics

(* a state is a prover state and its corresponding goal output here 
 * as a string *)
type state = {ps: Prover.state; output: string}

(* history is stack of state represented here with a list *)
type stack = state list

(* This is the initial prover state 
 * Loading Prelude.sp will fail since in full JS it can't access file
 * system *)
let prover_state : Prover.state ref = 
  ref (Prover.init ~withPrelude:false ())

let firstOutput = "Prover initial state : Ready to go !"

(* initial history is an stack with first prover state *) 
let prover_stack : (state list) ref = 
  ref [{ps = !prover_state;
        output = firstOutput}]

(* function that re-init state and history *)
let init () =
  prover_state := Prover.init ~withPrelude:false ();
  prover_state := Prover.do_set_option 
      !prover_state (TConfig.s_interactive,Config.Param_bool true);
  prover_stack := [{ps= !prover_state; output=firstOutput}]

(* push state in history *)
let push (s:state) : stack =
  let h' = s::(!prover_stack) in
  prover_stack := h';
  prover_state := s.ps;
  h'

exception Empty
exception TryToPopInit
(* pop state of history *)
let pop : stack * state =
  match !prover_stack with
  | [] -> raise Empty
  | s::h -> prover_stack := h;
            prover_state := s.ps;
            (h,s)

let rec popn' (i:int) (h:stack) (poped:state list) 
  : stack * state list =
  if i = 0 then (h,poped) else
  match h with
  | [] -> raise Empty
  | [_] -> raise TryToPopInit (* should not try to pop init state *)
  | s::h' -> popn' (i-1) h' (s::poped)

(* pop n states of history *)
let popn (i:int) : stack * state list = 
  let h',poped = popn' i !prover_stack [] in
  prover_stack := h';
  prover_state := (List.hd h').ps; (*should always have init state*)
  (h',poped)

(* get output of current state *)
let show () : string =
  let st = List.hd !prover_stack in
  st.output

(* get output of nth state *)
let shown (i:int) : string =
  let st = List.nth !prover_stack i in
  st.output

(* get actual formatter *)
let get_formatter = 
  Printer.get_std ()

(* print goal in actual buffer *)
let print_goal () = 
  match Prover.get_mode !prover_state with
  | ProverLib.ProofMode -> 
      Printer.prthtml `Goal "%a" (Prover.pp_goal !prover_state) ()
  | _ -> 
      Printer.prthtml `Goal "Nothing to show…"

(* FIXME ↓ this removes html style compare to print_goal, why ? *)
(* same as print_goal but print directly into a created buffer and
 * return the result string *)
let str_goal () : string =
  let buff = Buffer.create 16 in
  let formatter = Format.formatter_of_buffer buff in
  let _ = match Prover.get_mode !prover_state with
  | ProverLib.ProofMode -> 
      Printer.prthtml_out formatter `Goal "%a" (Prover.pp_goal
                                                  !prover_state) ()
  | _ -> 
    Printer.prthtml_out formatter `Goal "Nothing to show…" 
  in
  Format.pp_print_flush formatter ();
  Buffer.contents buff

(* this call print_goal and flush the result into a string that is
 * returned *)
let get_goal_print () : string = 
    print_goal (); (* will printout the current goal *)
    Format.flush_str_formatter ()

(* execute given sentence and return boolean true if everything is 
 * ok + the corresponding output *)
let exec_sentence ?(check=`Check) s : bool * string = 
  try
    prover_state := Prover.exec_all ~check !prover_state s;
    let info = Format.flush_str_formatter () in
    prover_stack := 
      push {ps= !prover_state; output= get_goal_print ()};
    (true,info)
  with e -> 
    Printer.prthtml `Error "Exec failed: %a"
      (Errors.pp_toplevel_error ~test:false 
         (Driver.file_from_str s)) e;
    (false,
     (* return the exception info as string *)
     Format.flush_str_formatter ())

(* execute given command and return the corresponding output *)
let exec_command ?(check=`Check) s : string = 
  try
    let _ = Prover.exec_command ~check s !prover_state in
    let info = Format.flush_str_formatter () in
    info
  with e -> 
    Printer.prthtml `Error "Run failed: %a"
      (Errors.pp_toplevel_error ~test:false 
         (Driver.file_from_str s)) e;
    Format.flush_str_formatter () (* will print the exception info *)

(* return visualisation as string *)
let visualisation () : string =
 try begin 
   match Prover.get_first_subgoal !prover_state with
   | Local j ->
         Format.asprintf "%a"
           Squirrelhtml.Visualisation.pp j
   | _ | exception _ -> 
       "{\"error\": \"Nothing to visualize\"}"
   end
  with _ -> 
    "{\"error\": \"Error for visualization.pp\"}"

(* we assume here that it's html formatted output *)
let _ =
  Printer.init Printer.Html
