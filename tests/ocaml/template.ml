(** Template for creating tests. *)

module Prover = Squirrelprover.Prover

module ProverLib = Squirrelcore.ProverLib

let template_test () =
  let st = Prover.init ~withPrelude:false () in
  (* let st = Prover.set_param st (C.s_post_quantum, (Co.Param_bool true)) in *)
  let st = 
    Prover.exec_all ~check:`Check ~test:true st
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

  Alcotest.(check' bool) 
    ~msg:"is proof completed ?" 
    ~expected:true
    ~actual:(Prover.is_proof_completed st);

  Alcotest.(check' bool) 
    ~msg:"mode is WaitQed ?" 
    ~expected:true
    ~actual:((Prover.get_mode st) = ProverLib.WaitQed);

  let st = Prover.exec_command ~check:`Check ~test:true "Qed." st in
  (* assert (Prover.current_goal_name st = None) *)
  Alcotest.(check some_testable) "Goal name" 
    (Prover.current_goal_name st) (None)

let tests = [ ("template", `Quick, Util.catch_error template_test);
            ]
