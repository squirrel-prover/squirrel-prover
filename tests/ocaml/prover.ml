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

  Alcotest.(check bool) "Subgoals empty" 
    ((Prover.get_subgoals st)=[]) true;

  let st = Prover.exec_command "Reset." st in
  Alcotest.(check some_testable) "Goal name" 
    (Prover.current_goal_name st) (None);

  Alcotest.(check bool) "prover_mode = GoalMode" 
    ((Prover.get_mode st)=ProverLib.GoalMode) true

(*------------------------------------------------------------------*)
let some_print () =
  let st = Prover.init () in
  (Prover.exec_all ~test:true st
     "include Logic.\n\
      channel c\n\
      system T = (S : !_i !_i new n; out(c,n)).\n\
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
      print yo." : Prover.state)
  |> ignore

let run_test () = 
  Prover.run ~test:true "tests/ok/test.sp"

(*------------------------------------------------------------------*)
let some_include () =
  let st = Prover.init () in
  (Prover.exec_all ~test:true st
     "include \"./Logic.sp\"." : Prover.state)
  |> ignore

(*------------------------------------------------------------------*)
let include_admit () =
  let st = Prover.init () in
  let st : Prover.state =
    Prover.exec_all ~test:true st
      "include[admit] \"tests/alcotest/badProof.sp\"."
  in
  ignore st

(*------------------------------------------------------------------*)
let tests = [
   ("Print",            `Quick, Util.catch_error some_print);
   ("Include",          `Quick, Util.catch_error some_include);
   ("Include[admit]",   `Quick, Util.catch_error include_admit);
   ("tests/ok/test.sp", `Quick, Util.catch_error run_test);
   ("Cycle by name", `Quick, Util.catch_error begin fun () ->
       Alcotest.check_raises "run test"
         (Squirrelcore.Command.Cmd_error (IncludeCycle "cyclename"))
         (fun () -> Prover.run ~test:true "tests/alcotest/cyclename.sp")
    end);
   ("Cycle by path", `Quick, Util.catch_error begin fun () ->
       Alcotest.check_raises "run test"
         (Squirrelcore.Command.Cmd_error (IncludeCycle "cyclepath"))
         (fun () -> Prover.run ~test:true "tests/alcotest/cyclepath.sp")
    end);
]
