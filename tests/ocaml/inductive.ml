module Prover = Squirrelprover.Prover

open Squirrelcore

(* open Util *)

(*------------------------------------------------------------------*)
let positivity () =
  let exception Ok in
  let st = Prover.init () in
  let st = 
    Prover.exec_all ~test:true st
      (* `a` positive, `b` negative *)
      "inductive arrow a b = U: (a -> b) -> arrow a b."
  in

  (*------------------------------------------------------------------*)
  (* positive tests *)
  ignore (
    Prover.exec_command ~test:true
      "inductive tau = C: (int -> tau) -> tau." st);

  ignore (
    Prover.exec_command ~test:true
      "inductive tau = C: (arrow int tau) -> tau." st);

  (*------------------------------------------------------------------*)
  (* negative tests *)
  Alcotest.check_raises "positivity restriction 1" Ok
    (fun () ->
       ignore (
         try Prover.exec_command ~test:true
               "inductive tau = C: (tau -> tau) -> tau." st
         with
         | ProcessDecl.Error (_,_,Failure _) -> raise Ok));

  Alcotest.check_raises "positivity restriction 2" Ok
    (fun () ->
       ignore (
         try Prover.exec_command ~test:true
               "inductive tau = C: (tau -> int) -> tau." st
         with
         | ProcessDecl.Error (_,_,Failure _) -> raise Ok));

  Alcotest.check_raises "positivity restriction 3" Ok
    (fun () ->
       ignore (
         try Prover.exec_command ~test:true
               "inductive tau = C: arrow tau tau -> tau." st
         with
         | ProcessDecl.Error (_,_,Failure _) -> raise Ok));

  Alcotest.check_raises "positivity restriction 4" Ok
    (fun () ->
       ignore (
         try Prover.exec_command ~test:true
               "inductive tau = C: arrow tau int -> tau." st
         with
         | ProcessDecl.Error (_,_,Failure _) -> raise Ok));
  ()



(*------------------------------------------------------------------*)
let tests = [
  "test1", `Quick, positivity;
]
