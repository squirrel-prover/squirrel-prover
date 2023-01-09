module Prover = Squirrellib.Prover
module ProverLib = Squirrellib.ProverLib
module Parser = Squirrellib.Parser
module Lexer = Squirrellib.Lexer
module Theory = Squirrellib.Theory

let term_from_string (s:string) = Theory.Local 
    (Parser.top_formula Lexer.token (Lexing.from_string s))

let sexpr_from_string (s:string) = (Parser.system_expr Lexer.token
                                     (Lexing.from_string s))
let search_about_1 () =
  let st = Prover.init () in
  (* let st = Prover.set_param st (C.s_post_quantum, (Co.Param_bool true)) in *)
  let st = 
    Prover.exec_command 
        "channel c
        system [T] (S : !_i new n; out(c,n))." st
    |> Prover.exec_command "goal [T] foo (i:index) : happens(S(i)) => output@S(i) = n(i)."
  |> Prover.exec_command "Proof."
  |> Prover.exec_command "search happens(_)."
  in
  let matches = Prover.search_about st 
      (ProverLib.Srch_term (term_from_string "happens(_)"))
  in
  Alcotest.(check int) "Found one lemma with happens(_)"
    (List.length matches) 1;

  Alcotest.(check int) "Found one pattern happens(_) in lemma"
    (List.length (snd (List.hd matches))) 1;
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
    (ProverLib.Srch_term (term_from_string "n(_)"))
  in
  Alcotest.(check int) "Found one lemma with n(_)"
    (List.length matches) 1;
  Alcotest.(check int) "Found one pattern n(_) in lemma"
    (List.length (snd (List.hd matches))) 1;

  let _ =  Prover.exec_command "search n(_)." st in
  ()

let search_about_2 () =
  let exception Ok in
  let exception Ko in
  let st = Prover.init () in
  (* let st = Prover.set_param st (C.s_post_quantum, (Co.Param_bool true)) in *)
  let st = Prover.exec_all st 
    "channel c
    name n : index->message
    system [S] (A : out(c,diff(zero,empty))).

    goal [S] foo (i:index) : happens(A) => output@A = diff(zero,zero).
    Proof.
      admit.
    Qed."
  in
  Alcotest.check_raises "search fail without context 1" Ok
      (fun () ->
        let _ = try Prover.exec_command "search input@A." st with
          | Squirrellib.Theory.Conv _ -> raise Ok in raise Ko);
  Alcotest.check_raises "search fail without context 2" Ok
      (fun () ->
        let _ = try Prover.exec_command "search output@A." st with
          | Squirrellib.Theory.Conv _ -> raise Ok in raise Ko);
  let _ = Prover.exec_command "search input@A in [S]." st in
  let _ = Prover.exec_command "search output@A in [S]." st in
  let matches = Prover.search_about st
    (ProverLib.Srch_inSys ((term_from_string "output@A"),
                           sexpr_from_string "[S]"))
  in
  Alcotest.(check bool) "Found one lemma with output@A"
    ((List.length matches)=1) true;
  (* works but no matches *)
  let _ = Prover.exec_command "search <_,_>." st in
  let _ = Prover.exec_command "search (_,_)." st in
  let st = Prover.exec_all st
    "global goal [S] myeq : equiv(true).
    Proof.
      admit.
    Qed."
  in
  (* FIXME parser doesn't want to parse equiv → keyword ? *)
  (* let _ = Prover.exec_command "search equiv(_) in [S]." st in *)
  (* Prover.do_search st *)
  (*   (ProverLib.Srch_inSys ((term_from_string "equiv(_)"), *)
  (*                          sexpr_from_string "[S]")); *)
  let _ = Prover.exec_command "search true in [S]." st in
  let matches = Prover.search_about st
    (ProverLib.Srch_inSys ((term_from_string "true"),
                           sexpr_from_string "[S]"))
  in
  Alcotest.(check int) "Found one lemma with true"
    (List.length matches) 1;
  (* Should print ↓ *)
  let _ = Prover.exec_command "print goal myeq." st in
  ()

let include_search () =
  let st = Prover.init () in
  (* let st = Prover.set_param st (C.s_post_quantum, (Co.Param_bool true)) in *)
  let st = 
    Prover.exec_all st
        "include Basic.
        channel c
        system [T] (S : !_i new n; out(c,n)).
        goal [T] foo (i:index) : happens(S(i)) => output@S(i) = n(i).   
        Proof."
  in
  let matches = Prover.search_about st 
      (ProverLib.Srch_term (term_from_string "happens(_)"))
  in
  Alcotest.(check int) "Found 2 lemmas with happens(_)"
    (List.length matches) 2;

  Alcotest.(check int) "Found one pattern happens(_) in lemma"
    (List.length (snd (List.hd matches))) 1;
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
    (ProverLib.Srch_term (term_from_string "n(_)"))
  in
  Alcotest.(check int) "Found one lemma with n(_)"
    (List.length matches) 1;
  Alcotest.(check int) "Found one pattern n(_) in lemma"
    (List.length (snd (List.hd matches))) 1;

  let matches = Prover.search_about st
    (ProverLib.Srch_term (term_from_string "<_,_>"))
  in
  Alcotest.(check int) "Found 2 lemmas with <_,_>"
    (List.length matches) 2;
  ()

let tests = [ ("search_about1", `Quick, search_about_1);
              ("search_about2", `Quick, search_about_2);
              ("include_search", `Quick, include_search);
            ]
