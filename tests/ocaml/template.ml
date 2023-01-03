module Prover = Squirrellib.Prover
(* module Parser = Squirrellib.Parser *)
(* module Lexer = Squirrellib.Lexer *)

let template_test () =
  let st = Prover.init () in
  (* let st = Prover.set_param st (C.s_post_quantum, (Co.Param_bool true)) in *)
  let st = 
    Prover.exec_command 
        "channel c
        system S : !_i new n; out(c,n)." st
  |> Prover.exec_command "goal foo (i:index) : happens(S(i)) => output@S(i) = n(i)."
  |> Prover.exec_command "Proof."
  |> Prover.exec_command "auto."
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

  let st = Prover.exec_command "Qed." st in
  (* assert (Prover.current_goal_name st = None) *)
  Alcotest.(check some_testable) "Goal name" 
    (Prover.current_goal_name st) (None)

let tests = [ ("template", `Quick, template_test);
            ]
