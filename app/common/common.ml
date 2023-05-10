open Squirrelprover
include Squirrelcore

(* Need to include it to register the tactics *)
include Squirreltactics

let prover_state : Prover.state ref = ref (Prover.init ())

let get_formatter = 
  Printer.get_std ()

let greet = function
  | `Server -> "Hello..."
  | `Client -> "...world!"

let exec_all s = 
  prover_state := Prover.exec_all !prover_state s

let exec_command s = 
  prover_state := Prover.exec_command s !prover_state 

let _ =
  Printer.init Printer.Html
