module Prover = Squirrellib.Prover
module Parser = Squirrellib.Parser
module Lexer = Squirrellib.Lexer

let search_about_test () =
  let st = Prover.init () in
  (* let st = Prover.set_param st (C.s_post_quantum, (Co.Param_bool true)) in *)
  let st = 
    Prover.exec_command 
        "channel c
        system S : !_i new n; out(c,n)." st
  |> Prover.exec_command "goal foo (i:index) : happens(S(i)) => output@S(i) = n(i)."
  |> Prover.exec_command "Proof."
  |> Prover.exec_command "search happens(_)."
  in
  let matches = Prover.search_about st
    (Parser.top_formula Lexer.token (Lexing.from_string "happens(_)"))
  in
  Alcotest.(check bool) "Found one lemma with happens(_)"
    ((List.length matches)=1) true;

  Alcotest.(check bool) "Found one pattern happens(_) in lemma"
    ((List.length (snd (List.hd matches)))=1) true;
  let st = Prover.exec_command "auto." st
  |> Prover.exec_command "Qed."
  in
  let pprint_option ppf = function 
    | Some s -> Fmt.pf ppf "%s" s
    | None -> Fmt.pf ppf "" in
  let some_testable = Alcotest.testable pprint_option (=) in
  Alcotest.(check some_testable) "Goal name" 
    (Prover.current_goal_name st) (None);

  let matches = Prover.search_about st
    (Parser.top_formula Lexer.token (Lexing.from_string "n(_)"))
  in
  Alcotest.(check bool) "Found one lemma with n(_)"
    ((List.length matches)=1) true;
  Alcotest.(check bool) "Found one pattern n(_) in lemma"
    ((List.length (snd (List.hd matches)))=1) true

let tests = [ ("search_about", `Quick, search_about_test);
            ]
