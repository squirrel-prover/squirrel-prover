module Prover = Squirrelprover.Prover

open Squirrelcore

(* open Util *)

(*------------------------------------------------------------------*)
let test1 () =
  let exception Ok in
  let st = Prover.init () in
  let st = 
    Prover.exec_all ~test:true st
      "channel c.
      system null.
      predicate Foo  ['a] {} (x : 'a) y z = [x = y && y = z].
      global axiom _ ['a] (x,y,z : 'a) : $(Foo x y z)."
  in
  Alcotest.check_raises "type mismatch" Ok
    (fun () ->
       ignore (
         try Prover.exec_command ~test:true
               "global axiom _ ['a] (x,y,z : 'a) : $(Foo x y empty)." st
         with
         | Theory.Conv _ -> raise Ok));
  Alcotest.check_raises "no multi-term: diff" Ok
    (fun () ->
       ignore (
         try Prover.exec_command ~test:true
               "global axiom _ ['a] (x,y,z : 'a) : $(Foo x y (diff(x,y)))." st
         with
         | Theory.Conv _ -> raise Ok));
  Alcotest.check_raises "no multi-term: macro" Ok
    (fun () ->
       ignore (
         try Prover.exec_command ~test:true
               "global axiom _  : $(Foo empty empty (frame@init))." st
         with
         | Theory.Conv _ -> raise Ok));

  ()



(*------------------------------------------------------------------*)
let tests = [
  "test1", `Quick, test1;
]
