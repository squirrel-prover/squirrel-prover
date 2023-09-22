(** Testing various commands of the prover: search, print, include. *)

module Prover = Squirrelprover.Prover
module ProverLib = Squirrelcore.ProverLib

(*------------------------------------------------------------------*)
let reset_test () =
  let st = Prover.init () in
  (* let st = Prover.set_param st (C.s_post_quantum, (Co.Param_bool true)) in *)
  let st = 
    Prover.exec_all st
        "channel c
        system S : !_i new n; out(c,n).
        lemma foo (i:index) : happens(S(i)) => output@S(i) = n(i).
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
  let st = Prover.init () in
  Prover.exec_all ~test:true st
    "include Basic.\n\
     channel c\n\
     system [T] (S : !_i !_i new n; out(c,n)).\n\
     lemma [T] foo (i:index) : happens(S(i,i)) => output@S(i,i) = n(i,i).\n\
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
let some_include () =
  let st = Prover.init () in
  Prover.exec_all ~test:true st
    "include \"./Basic.sp\"."
  |> ignore

(*------------------------------------------------------------------*)
let tests = [
   ("some_print",         `Quick, Util.catch_error some_print);
   ("some_include",       `Quick, Util.catch_error some_include);
   ("run_test",           `Quick, Util.catch_error run_test);
]
