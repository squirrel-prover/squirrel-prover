(** Testing various commands of the prover: search, print, include. *)

module TopLevel = Squirreltop.TopLevel
module Prover = Squirrelprover.Prover
module TProver = TopLevel.Make(Prover)
module ProverLib = Squirrelcore.ProverLib
module Theory = Squirrelcore.Theory

(*------------------------------------------------------------------*)
let some_print () =
  let exception Ok in
  Alcotest.check_raises "print stuff" Ok
    (fun () ->
      let st = TProver.init () in
      let _ = try TProver.exec_all ~test:true st
        "include Prelude.
         include Basic.
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

(* let run_test () =  *)
(*   let exception Ok in *)
(*   Alcotest.check_raises "run test" Ok *)
(*     (fun () -> *)
(*        let _ = TProver.run ~test:true "tests/ok/test.sp" in *)
(*        raise Ok *)
(*     ) *)

let compare_runner () = 
  let t = Sys.time() in
  let _ = TProver.run ~test:true "examples/lak-tags-full-wa.sp" in
  let t1 = Sys.time() -. t in
  Printf.printf "Execution time Prover: %fs\n" t1;
  let t = Sys.time() in
  let _ = Squirrellib.Main.run ~test:true "examples/lak-tags-full-wa.sp" in
  let t2 = Sys.time() -. t in
  Printf.printf "Execution time Main: %fs\n" t2;
  Alcotest.(check' bool) ~msg:"Prover faster ?" 
    ~actual:(t1<t2) ~expected:true;
  Alcotest.(check' bool) ~msg:"Prover slower ?" 
    ~actual:(t1>t2) ~expected:true

(*------------------------------------------------------------------*)
let tests = [ ("some_print",         `Quick, some_print);
              (* ("run_test",           `Quick, run_test); *)
              (* ("compare_runner",     `Quick, compare_runner); *)
            ]
