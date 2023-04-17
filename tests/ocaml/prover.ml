(** Testing various commands of the prover: search, print, include. *)

module Prover = Squirrellib.Prover
module ProverLib = Squirrellib.ProverLib
module Theory = Squirrellib.Theory

open Util

(*------------------------------------------------------------------*)
let reset_test () =
  let st = Prover.init () in
  (* let st = Prover.set_param st (C.s_post_quantum, (Co.Param_bool true)) in *)
  let st = 
    Prover.exec_all st
        "channel c
        system S : !_i new n; out(c,n).
        goal foo (i:index) : happens(S(i)) => output@S(i) = n(i).
        Proof.
          auto."
  in
  let pprint_option ppf = function 
    | Some s -> Fmt.pf ppf "%s" s
    | None -> Fmt.pf ppf "" in
  let some_testable = Alcotest.testable pprint_option (=) in
  Alcotest.(check some_testable) "Goal name" 
    (Prover.current_goal_name st) (Some "foo");
  (* assert (Prover.current_goal_name st = Some "foo"); *)
  Alcotest.(check bool) "Subgoals empty" 
    ((Prover.get_subgoals st)=[]) true;
  (* assert (Prover.get_subgoals st = []); *)

  let st = Prover.exec_command "Reset." st in
  (* assert (Prover.current_goal_name st = None) *)
  Alcotest.(check some_testable) "Goal name" 
    (Prover.current_goal_name st) (None);

  (* assert (Prover.prover_mode = GoalMode) *)
  Alcotest.(check bool) "prover_mode = GoalMode" 
    ((Prover.get_mode st)=ProverLib.GoalMode) true

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

let run_test () = 
  let exception Ok in
  Alcotest.check_raises "run test" Ok
    (fun () ->
       let _ = Prover.run ~test:true "tests/ok/test.sp" in
       raise Ok
    )

let compare_runner () = 
  let t = Sys.time() in
  let _ = Prover.run ~test:true "examples/lak-tags-full-wa.sp" in
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
              ("run_test",           `Quick, run_test);
              (* ("compare_runner",     `Quick, compare_runner); *)
            ]
