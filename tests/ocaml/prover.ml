(** Testing various commands of the prover: search, print, include. *)

module Prover = Squirrelprover.Prover

(*------------------------------------------------------------------*)
let some_print () =
  let st = Prover.init () in
  Prover.exec_all ~test:true st
    "include Basic.\n\
     channel c\n\
     system [T] (S : !_i !_i new n; out(c,n)).\n\
     goal [T] foo (i:index) : happens(S(i,i)) => output@S(i,i) = n(i,i).\n\
     Proof.\n\
       admit.\n\
     Qed.\n\
     print n.\n\
     print cond.\n\
     print happens.\n\
     print coucou.\n\
     print foo.\n\
     name yo:message.\n\
     print yo."
  |> ignore

let run_test () = 
  let exception Ok in
  Alcotest.check_raises "run test" Ok
    (fun () ->
       let _ = Prover.run ~test:true "tests/ok/test.sp" in
       raise Ok
    )

(*------------------------------------------------------------------*)
let tests = [
   ("some_print",         `Quick, some_print);
   ("run_test",           `Quick, run_test);
]
