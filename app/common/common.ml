(* A Prover driver with history and with web formatted output
 *
 * TODO :
 * - a start for client-server squirrel on browser
 *)

include Squirrelcore
include Squirrelprover
module L = Location
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
let prover_state : Prover.state option ref = ref None

let firstOutput = "Prover initial state : Ready to go !"

(* initial history is an stack with first prover state *) 
let prover_stack : (state list) option ref = ref None
(* function that re-init state and history *)
let init s =
  let init_state = Prover.init ~with_string_prelude:(Some s) () in
  prover_state := Some (Prover.do_set_option 
      init_state (L.mk_loc L._dummy TConfig.s_interactive, TConfig.Param_bool true));
  prover_stack := Some [{ps= init_state; output=firstOutput}]


exception NonInit
  
let get_stack_or_fail () =
  match !prover_stack with
  |None -> raise NonInit
  | Some s-> s

let get_state_or_fail () =
  match !prover_state with
  |None -> raise NonInit
  | Some s-> s


(* push state in history *)
let push (s:state) : stack =
  let h' = s::(get_stack_or_fail ()) in
  prover_stack := Some h';
  prover_state := Some s.ps;
  h'

exception Empty
exception TryToPopInit
(* pop state of history *)
(* let pop : stack * state =
  match !prover_stack with
  | Some [] -> raise Empty
  | Some (s::h) -> prover_stack := Some h;
            prover_state := Some s.ps;
    (h,s)
  | None -> raise NonInit
*)
let rec popn' (i:int) (h:stack) (poped:state list) 
  : stack * state list =
  if i = 0 then (h,poped) else
  match h with
  | [] -> raise Empty
  | [_] -> raise TryToPopInit (* should not try to pop init state *)
  | s::h' -> popn' (i-1) h' (s::poped)

(* pop n states of history *)
let popn (i:int) : stack * state list = 
  let h',poped = popn' i (get_stack_or_fail ()) [] in
  prover_stack := Some h';
  prover_state := Some (List.hd h').ps; (*should always have init state*)
  (h',poped)

(* get output of current state *)
let show () : string =
  let st = List.hd (get_stack_or_fail ()) in
  st.output

(* get output of nth state *)
let shown (i:int) : string =
  let st = List.nth (get_stack_or_fail ()) i in
  st.output

(* get actual formatter *)
let get_formatter = 
  Printer.get_std ()

(* print goal in actual buffer *)
let print_goal () = 
  match Prover.get_mode (get_state_or_fail ()) with
  | ProverLib.ProofMode -> 
    Printer.prthtml `Goal "%a" Prover.pp_goal (get_state_or_fail ())
      
  | _ | exception NonInit -> 
      Printer.prthtml `Goal "Nothing to show…"

(* FIXME ↓ this removes html style compare to print_goal, why ? *)
(* same as print_goal but print directly into a created buffer and
 * return the result string *)
let str_goal () : string =
  let buff = Buffer.create 16 in
  let formatter = Format.formatter_of_buffer buff in
  let _ = match Prover.get_mode (get_state_or_fail ()) with
  | ProverLib.ProofMode -> 
      Printer.prthtml_out formatter `Goal "%a" Prover.pp_goal (get_state_or_fail ())
  | _ | exception NonInit  -> 
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
    prover_state := Some (Prover.exec_all ~check (get_state_or_fail ()) s);
    let info = Format.flush_str_formatter () in
    prover_stack := Some (
      push {ps= (get_state_or_fail ()); output= get_goal_print ()});
    (true,info)
  with e -> 
    Printer.prthtml `Error "Exec failed: %a"
      (Errors.pp_toplevel_error ~test:false         
         (Driver.from_string s)
         (Prover.get_table (get_state_or_fail ()))
      ) e;
    (false,
     (* return the exception info as string *)
     Format.flush_str_formatter ())

(* execute given command and return the corresponding output *)
let exec_command ?(check=`Check) s : string = 
  try
    let _ = Prover.exec_command ~check s (get_state_or_fail ()) in
    let info = Format.flush_str_formatter () in
    info
  with e -> 
    Printer.prthtml `Error "Run failed: %a"
      (Errors.pp_toplevel_error ~test:false
         (Driver.from_string s) (Prover.get_table (get_state_or_fail ()))) e;
    Format.flush_str_formatter () (* will print the exception info *)

(* return visualisation as string *)
let visualisation () : string =
 try begin 
   match Prover.get_first_subgoal (get_state_or_fail ()) with
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
