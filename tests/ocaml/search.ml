module Prover = Squirrelprover.Prover
module ProverLib = Squirrelcore.ProverLib

open Util

(*------------------------------------------------------------------*)
let search_unify () =
  let exception Ok in
  Alcotest.check_raises "unify Names with special arity when search" Ok
    (fun () ->
      let st = Prover.init ~withPrelude:false () in
      let st = try Prover.exec_all ~test:true st
        "channel c
        system [T] (S : !_i !_i new n; out(c,n)).
        lemma [T] foo (i:index) : happens(S(i,i)) => output@S(i,i) = n(i,i).
        Proof.
        admit.
        Qed.
        search len(_).
        search n(_).
        search n(_,_).
        name yo:message."
      with | e -> raise e in
      let matches = Prover.search_about st
          (ProverLib.Srch_term (term_from_string "len(_)"))
      in
      Alcotest.(check' int) ~msg:"Found one axiom with len(_)" 
        ~actual:(List.length matches) ~expected:2;
      let matches = Prover.search_about st 
          (ProverLib.Srch_term (term_from_string "n(_)"))
      in
      Alcotest.(check' int) ~msg:"Found one axiom with n(_)" 
        ~actual:(List.length matches) ~expected:2;
      let matches = Prover.search_about st
          (ProverLib.Srch_term (term_from_string "n(_,_)"))
      in
      Alcotest.(check' int) ~msg:"Found one axiom with n(_,_)" 
        ~actual:(List.length matches) ~expected:1;
      let matches = Prover.search_about st
          (ProverLib.Srch_term (term_from_string "len(yo)"))
      in
      Alcotest.(check' int) ~msg:"Found one axiom with len(yo)" 
        ~actual:(List.length matches) ~expected:1;
      raise Ok
    )

(*------------------------------------------------------------------*)
let search_about_1 () =
  let st = Prover.init ~withPrelude:false () in
  (* let st = Prover.set_param st (C.s_post_quantum, (Co.Param_bool true)) in *)
  let st = 
    Prover.exec_command ~test:true 
        "channel c
        system [T] (S : !_i new n; out(c,n))." st
    |> Prover.exec_command ~test:true
         "lemma [T] foo (i:index) : happens(S(i)) => output@S(i) = n(i)."
  |> Prover.exec_command ~test:true "Proof."
  |> Prover.exec_command ~test:true "search happens(_)."
  in
  let matches = Prover.search_about st
      (ProverLib.Srch_term (term_from_string "happens(_)"))
  in
  Alcotest.(check' int) ~msg:"Found one lemma with happens(_)" 
    ~actual:(List.length matches) ~expected:1;

  Alcotest.(check' int) ~msg:"Found one pattern happens(_) in lemma"
    ~actual:(List.length (snd (List.hd matches))) ~expected:1;
  let st = Prover.exec_command ~test:true "auto." st
  |> Prover.exec_command ~test:true "Qed."
  in
  let pprint_option ppf = function 
    | Some s -> Fmt.pf ppf "%s" s
    | None -> Fmt.pf ppf "" in
  let some_testable = Alcotest.testable pprint_option (=) in
  Alcotest.(check' some_testable) ~msg:"Goal name" 
    ~actual:(Prover.current_goal_name st) ~expected:(None);

  let matches = Prover.search_about st
    (ProverLib.Srch_term (term_from_string "n(_)"))
  in
  Alcotest.(check' int) ~msg:"Found one lemma with n(_)"
    ~actual:(List.length matches) ~expected:2;
  Alcotest.(check' int) ~msg:"Found one pattern n(_) in lemma"
    ~actual:(List.length (snd (List.hd matches))) ~expected:1;

  let _ =  Prover.exec_command ~test:true "search n(_)." st in
  ()

(*------------------------------------------------------------------*)
let search_about_2 () =
  let exception Ok in
  let exception Ko in
  let st = Prover.init ~withPrelude:false () in
  (* let st = Prover.set_param st (C.s_post_quantum, (Co.Param_bool true)) in *)
  let st = Prover.exec_all ~test:true st 
    "channel c
    name n : index->message
    system [S] (A : out(c,diff(zero,empty))).

    lemma [S] foo (i:index) : happens(A) => output@A = diff(zero,zero).
    Proof.
      admit.
    Qed."
  in
  Alcotest.check_raises "search fail without context 1" Ok
      (fun () ->
        let _ = try Prover.exec_command ~test:true "search input@A." st with
          | Squirrelcore.Theory.Conv _ -> raise Ok in raise Ko);
  Alcotest.check_raises "search fail without context 2" Ok
      (fun () ->
        let _ = try Prover.exec_command ~test:true "search output@A." st with
          | Squirrelcore.Theory.Conv _ -> raise Ok in raise Ko);
  let _ = Prover.exec_command ~test:true "search input@A in [S]." st in
  let _ = Prover.exec_command ~test:true "search output@A in [S]." st in
  let matches = Prover.search_about st
    (ProverLib.Srch_inSys ((term_from_string "output@A"),
                           sexpr_from_string "[S]"))
  in
  Alcotest.(check int) "Found one lemma with output@A"
    1 (List.length matches);
  (* works but no matches *)
  let _ = Prover.exec_command ~test:true "search <_,_>." st in
  let _ = Prover.exec_command ~test:true "search (_,_)." st in
  let st = Prover.exec_all ~test:true st
    "global lemma [S] myeq : equiv(true).
    Proof.
      admit.
    Qed."
  in
  let matches = Prover.search_about st
    (ProverLib.Srch_inSys ((global_formula_from_string "equiv(_)"),
                           sexpr_from_string "[S]"))
  in
  Alcotest.(check' int) ~msg:"Found one lemma with equiv(_)"
    ~expected:1 ~actual:(List.length matches);
  let _ = Prover.exec_command ~test:true "search true in [S]." st in
  let matches = Prover.search_about st
    (ProverLib.Srch_inSys ((term_from_string "true"),
                           sexpr_from_string "[S]"))
  in
  Alcotest.(check' int) ~msg:"Found one lemma with true"
    ~expected:1 ~actual:(List.length matches);
  (* Should print ↓ *)
  let _ = Prover.exec_command ~test:true "print myeq." st in
  ()

(*------------------------------------------------------------------*)
let search_about_type_holes_1 () =
  let exception Ok in
  Alcotest.check_raises "search with type holes 1" Ok
    (fun () ->
      let st = Prover.init ~withPrelude:false () in
      let st = try Prover.exec_all ~test:true st
        "axiom [any] bar1 ['a] : exists (x : 'a), true.
         axiom [any] bar2 ['a] : exists (x : 'a -> 'a), true."
      with e -> raise e in

      (* test 1 *)
      let matches = Prover.search_about st
          (ProverLib.Srch_term (term_from_string "exists (x : _), _"))
      in
      Alcotest.(check' int) ~msg:"Test 1" 
        ~actual:(List.length matches) ~expected:2;

      (* test 2 *)
      let matches = Prover.search_about st
          (ProverLib.Srch_term (term_from_string "exists (x : _ -> _), _"))
      in
      Alcotest.(check' int) ~msg:"Test 2" 
        ~actual:(List.length matches) ~expected:1;

      raise Ok
    )

(*------------------------------------------------------------------*)
let search_about_type_holes_2 () =
  let exception Ok in
    Alcotest.check_raises "search with type holes 2" Ok
    (fun () ->
      let st = Prover.init ~withPrelude:false () in
      let st = try Prover.exec_all ~test:true st
        "axiom [any] foo ['a] (phi:'a -> bool) :
         (not (exists (a:'a), (phi a))) = (forall (a:'a), not (phi a)).

         axiom [any] bar ['a] (phi:bool) :
         (not (exists (a:'a), (phi))) = (forall (a:'a), not (phi))."
      with e -> raise e in

      (* test 1 *)
      let matches = Prover.search_about st
          (ProverLib.Srch_term
             (term_from_string "(not (exists (a:_), _ a)) = (forall (a:_), not (_ a))"))
      in
      Alcotest.(check' int) ~msg:"Test 1" 
        ~actual:(List.length matches) ~expected:2;

      (* test 2 *)
      let matches = Prover.search_about st
          (ProverLib.Srch_term
             (term_from_string "(not (exists (a:_), _ a)) = (forall (a:_), not  _   )"))
      in
      Alcotest.(check' int) ~msg:"Test 2" 
        ~actual:(List.length matches) ~expected:2;

      (* test 3 *)
      let matches = Prover.search_about st
          (ProverLib.Srch_term
             (term_from_string "(not (exists  _   , _ _)) = (forall  _   , _   (_ _))"))
      in
      Alcotest.(check' int) ~msg:"Test 3" 
        ~actual:(List.length matches) ~expected:1;

      (* test 4 *)
      let matches = Prover.search_about st
          (ProverLib.Srch_term
             (term_from_string "(not (exists  _   ,   _)) = (forall  _   ,         _)"))
      in
      Alcotest.(check' int) ~msg:"Test 4" 
        ~actual:(List.length matches) ~expected:2;

      raise Ok
    )

(*------------------------------------------------------------------*)
let include_search () =
  let st = Prover.init () in
  (* let st = Prover.set_param st (C.s_post_quantum, (Co.Param_bool true)) in *)
  let st = 
    Prover.exec_all ~test:true st
        "include Basic.
        channel c
        system [T] (S : !_i new n; out(c,n)).
        lemma [T] foo (i:index) : happens(S(i)) => output@S(i) = n(i).   
        Proof."
  in
  let matches = Prover.search_about st
      (ProverLib.Srch_term (term_from_string "happens(_)"))
  in
  Alcotest.(check' int) ~msg:"Found 2 lemmas with happens(_)"
    ~expected:2 ~actual:(List.length matches);

  Alcotest.(check' int) ~msg:"Found one pattern happens(_) in lemma"
    ~expected:1 ~actual:(List.length (snd (List.hd matches)));
  let st = Prover.exec_command ~test:true "auto." st
  |> Prover.exec_command ~test:true "Qed."
  in
  let pprint_option ppf = function 
    | Some s -> Fmt.pf ppf "%s" s
    | None -> Fmt.pf ppf "" in
  let some_testable = Alcotest.testable pprint_option (=) in
  Alcotest.(check' some_testable) ~msg:"Goal name" 
    ~actual:(Prover.current_goal_name st) ~expected:(None);

  let matches = Prover.search_about st
    (ProverLib.Srch_term (term_from_string "n(_)"))
  in
  Alcotest.(check' int) ~msg:"Found one lemma with n(_)"
    ~actual:(List.length matches) ~expected:2;
  Alcotest.(check' int) ~msg:"Found one pattern n(_) in lemma"
    ~actual:(List.length (snd (List.hd matches))) ~expected:1;

  let matches = Prover.search_about st
    (ProverLib.Srch_term (term_from_string "<_,_>"))
  in
  Alcotest.(check' int) ~msg:"Found 2 lemmas with <_,_>"
    ~actual:(List.length matches) ~expected:2;
  ()

(*------------------------------------------------------------------*)
let include_ite () =
  let st = Prover.init ~withPrelude:false () in
  (* let st = Prover.set_param st (C.s_post_quantum, (Co.Param_bool true)) in *)
  let st = 
    Prover.exec_all ~test:true st
        "
        lemma [any] if_true ['a] (b : boolean, x,y : 'a):
         b => if b then x else y = x.
        Proof.
          intro *.
          case (if b then x else y).
          + auto.
          + intro [HH _]. by use HH.
        Qed.

        lemma [any] if_true0 ['a] (x,y : 'a):
         if true then x else y = x.
        Proof.
          by rewrite if_true. 
        Qed.
        hint rewrite if_true0.

        lemma [any] if_false ['a] (b : boolean, x,y : 'a):
         (not b) => if b then x else y = y.
        Proof. 
          intro *; case (if b then x else y).
          + intro [H1 H2]. 
            by rewrite H1 in H2. 
          + auto.
        Qed.

        lemma [any] if_false0 ['a] (x,y : 'a):
         if false then x else y = y.
        Proof.
          by rewrite if_false.
        Qed.
        hint rewrite if_false0.

        channel c
        system [T] (S : !_i new n; out(c,n)).
        lemma [T] foo (i:index) : happens(S(i)) => output@S(i) = n(i).   
        Proof.
         admit.
        Qed."
  in
  let matches = Prover.search_about st
      (ProverLib.Srch_inSys ((term_from_string "happens(_)"),
                           sexpr_from_string "[T]"))
  in
  Alcotest.(check' int) ~msg:"Found 3 lemmas with happens(_) in [T]"
    ~actual:(List.length matches) ~expected:2;
  let matches = Prover.search_about st
    (ProverLib.Srch_term (term_from_string "if _ then _ else _ "))
  in
  Alcotest.(check' int) ~msg:"Found one lemma with if _ then _ else _"
    ~actual:(List.length matches) ~expected:4


(*------------------------------------------------------------------*)
let tests = [ ("search_about1",      `Quick, Util.catch_error search_about_1);
              ("search_about2",      `Quick, Util.catch_error search_about_2);
              ("search_type_holes1", `Quick, Util.catch_error search_about_type_holes_1);
              ("search_type_holes2", `Quick, Util.catch_error search_about_type_holes_2);
              ("include_search",     `Quick, Util.catch_error include_search);
              ("include_ite",        `Quick, Util.catch_error include_ite);
              ("search_unify",       `Quick, Util.catch_error search_unify);
            ]
