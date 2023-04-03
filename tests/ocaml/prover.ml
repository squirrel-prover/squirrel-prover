(** Testing various commands of the prover: search, print, include. *)

module Prover = Squirrellib.Prover
module ProverLib = Squirrellib.ProverLib
module Theory = Squirrellib.Theory

open Util

(*------------------------------------------------------------------*)
let some_print () =
  let exception Ok in
  Alcotest.check_raises "print stuff" Ok
    (fun () ->
      let st = Prover.init () in
      let _ = try Prover.exec_all st
        "include Basic.
        channel c
        system [T] (S : !_i !_i new n; out(c,n)).
        goal [T] foo (i:index) : happens(S(i,i)) => output@S(i,i) = n(i,i).
        Proof.
        admit.
        Qed.
        print n.
        print cond.
        print happens.
        print coucou.
        print foo.
        name yo:message.
        print yo."
      with | e -> raise e in
      raise Ok
    )

(*------------------------------------------------------------------*)
let tests = [ ("some_print",         `Quick, some_print);
            ]
