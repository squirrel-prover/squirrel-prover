(** Checking various tactics: case study, namelength. *)

open Squirrelcore
open Util
module ES = EquivSequent
module TS = TraceSequent
module L = Location

module Prover = Squirrelprover.Prover

let pprint_option ppf = function 
  | Some s -> Fmt.pf ppf "%s" s
  | None -> Fmt.pf ppf ""

let string_testable = Alcotest.testable pprint_option (=)

let term_testable = Alcotest.testable (Term.pp_dbg) (Term.equal)
let sys_testable table = Alcotest.testable (SystemExpr.pp)
    (SystemExpr.equal table)

let get_seq_in_nth_goal st i =
  let subgoals = Prover.get_subgoals st in
  let g = List.nth subgoals i in
  match g with
  | Goal.Global j -> ES.conclusion_as_equiv j
  | _ -> assert false

let mk c = L.mk_loc L._dummy c

let mk_message st s =
  let n = Symbols.Name.of_lsymb (mk s) (Prover.get_table st) in
  Term.mk_name (Term.mk_symb n Message) []

(** Check that case study fails when there is no conditional
    with the target condition. *)
let case_study_fail () =
  let st = Prover.init ~withPrelude:false () in
  let st =
    Prover.exec_all ~test:true st
      "name n : message.\n\
       name m : message.\n\
       system null.\n\
       global lemma _ : equiv(if true then diff(n,m)).\n\
       Proof."
  in
  try
    ignore (Prover.exec_command ~test:true "nosimpl cs false." st) ;
    Alcotest.failf "Tactic application should have failed."
  with
  | Tactics.(Tactic_soft_failure (_,Failure e)) ->
      Alcotest.(check' string)
        ~msg:"error message"
        ~expected:"did not find any conditional to analyze"
        ~actual:e;
  try
    ignore (Prover.exec_command ~test:true "nosimpl cs (if true then _)." st) ;
    Alcotest.failf "Tactic application should have failed with bad
    arguments."
  with
  | Tactics.(Tactic_soft_failure (_,Failure e)) ->
      Alcotest.(check' string)
        ~msg:"error message"
        ~expected:"Argument of cs should match a boolean"
        ~actual:e

(** Check that case study fails when there is no conditional
    with the target condition in the target item. *)
let case_study_fail' () =
  let st = Prover.init ~withPrelude:false () in
  let st =
    Prover.exec_all ~test:true st
      "name n : message.\n\
       name m : message.\n\
       system null.\n\
       global lemma _ :\n\
         equiv(if true then diff(n,m), if n=m then diff(n,m)).\n\
       Proof."
  in
  (* "cs true" works in 0 but not in 1 *)
  ignore (Prover.exec_command ~test:true "nosimpl cs true in 0." st) ;
  try
    ignore (Prover.exec_command ~test:true "nosimpl cs true in 1." st) ;
    Alcotest.failf "Tactic application should have failed."
  with
  | Tactics.(Tactic_soft_failure (_,Failure e)) ->
      Alcotest.(check' string)
        ~msg:"error message"
        ~expected:"did not find any conditional to analyze"
        ~actual:e

(** Check that case study works as expected on several examples. *)
let case_study () =

  let st = Prover.init ~withPrelude:false () in
  let st = 
    Prover.exec_all ~test:true st
        "mutable state : message = empty.
        name nfresh : message.
        system null.

        global lemma _ : equiv(if true then zero else empty).
        Proof."
  in

  (* Attention, simpl va trivialiser ce but. *)
  let st = Prover.exec_command ~test:true "nosimpl cs true." st in
  Printer.pr "%a" (Prover.pp_subgoals st) ();
  let terms = get_seq_in_nth_goal st 0 in
  Alcotest.(check' term_testable) 
    ~msg:"if true then zero else empty → true,ZERO"
    ~actual:(List.hd terms)
    ~expected:(Term.mk_zero);
  Alcotest.(check' term_testable) 
    ~msg:"if true then zero else empty → TRUE,zero"
    ~actual:(List.nth terms 1)
    ~expected:(Term.mk_true);

  let terms = get_seq_in_nth_goal st 1 in
  Alcotest.(check' term_testable) 
    ~msg:"if true then zero else empty → true,EMPTY"
    ~actual:(List.hd terms)
    ~expected:(Term.empty);
  Alcotest.(check' term_testable) 
    ~msg:"if true then zero else empty → TRUE,empty"
    ~actual:(List.nth terms 1)
    ~expected:(Term.mk_true);

  (* deux sous-buts, l'un avec true,zero, l'autre true,empty *)
  let st = Prover.exec_all ~test:true st
        "Abort.

        name n : message.
        name m : message.

        global lemma _ : equiv(if true then zero else empty, if true then n else m).
        Proof."
  in
  (* Attention, simpl va trivialiser ce but. *)
  let st = Prover.exec_command ~test:true "nosimpl cs true." st in
  Printer.pr "%a" (Prover.pp_subgoals st) ();
  (* deux sous-buts, l'un avec equiv(true,zero,n) l'autre equiv(true,empty,m) *)
  let terms = get_seq_in_nth_goal st 0 in
  Alcotest.(check' term_testable) 
    ~msg:"equiv(if true then zero else empty, if true then n else m) → true,ZERO,n"
    ~actual:(List.hd terms)
    ~expected:(Term.mk_zero);
  let n = mk_message st "n" in
  Alcotest.(check' term_testable) 
    ~msg:"if true then zero else empty → true,zero,N"
    ~actual:(List.nth terms 1)
    ~expected:(n);
  Alcotest.(check' term_testable) 
    ~msg:"equiv(if true then zero else empty, if true then n else m) → TRUE,zero,n"
    ~actual:(List.nth terms 2)
    ~expected:(Term.mk_true);

  let terms = get_seq_in_nth_goal st 1 in
  Alcotest.(check' term_testable) 
    ~msg:"equiv(if true then zero else empty, if true then n else m) →
    true,EMPTY,m"
    ~actual:(List.hd terms)
    ~expected:(Term.empty);
  let m = mk_message st "m" in
  Alcotest.(check' term_testable) 
    ~msg:"if true then zero else empty → true,empty,M"
    ~actual:(List.nth terms 1)
    ~expected:(m);
  Alcotest.(check' term_testable) 
    ~msg:"equiv(if true then zero else empty, if true then n else m) →
    TRUE,empty,m"
    ~actual:(List.nth terms 2)
    ~expected:(Term.mk_true);

  let st = Prover.exec_all ~test:true st
        "Abort.

        global lemma _ : 
          equiv(
                if true then zero else empty, 
                if true then n else m
                ).
        Proof."
  in
  (* Attention, simpl va trivialiser ce but. *)
  let st = Prover.exec_command ~test:true "nosimpl cs true in 1." st in
  Printer.pr "%a" (Prover.pp_subgoals st) ();
  (* deux sous-buts, equiv(true,if true then zero else empty,n)
     et  equiv(true,if true then zero else empty,m) *)
  let terms = get_seq_in_nth_goal st 0 in
  Alcotest.(check' term_testable) 
    ~msg:"equiv(if true then zero else empty, if true then n else m) → 
    true,
    IF TRUE THEN ZERO ELSE EMPTY,
    n"
    ~actual:(List.hd terms)
    ~expected:(Term.mk_ite ~simpl:false (Term.mk_true) (Term.mk_zero) (Term.empty));
  Alcotest.(check' term_testable) 
    ~msg:"equiv(if true then zero else empty, if true then n else m) → 
    TRUE,
    if true then zero else empty,
    n"
    ~actual:(List.nth terms 1)
    ~expected:(Term.mk_true);
  Alcotest.(check' term_testable) 
    ~msg:"equiv(if true then zero else empty, if true then n else m) → 
    true,
    if true then zero else empty,
    N"
    ~actual:(List.nth terms 2)
    ~expected:(n);

  let terms = get_seq_in_nth_goal st 1 in
  Alcotest.(check' term_testable) 
    ~msg:"equiv(if true then zero else empty, if true then n else m) → 
    true,
    IF TRUE THEN ZERO ELSE EMPTY,
    m"
    ~actual:(List.hd terms)
    ~expected:(Term.mk_ite ~simpl:false (Term.mk_true) (Term.mk_zero) (Term.empty));
  Alcotest.(check' term_testable) 
    ~msg:"equiv(if true then zero else empty, if true then n else m) → 
    TRUE,
    if true then zero else empty,
    m"
    ~actual:(List.nth terms 1)
    ~expected:(Term.mk_true);
  Alcotest.(check' term_testable) 
    ~msg:"equiv(if true then zero else empty, if true then n else m) → 
    true,
    if true then zero else empty,
    M"
    ~actual:(List.nth terms 2)
    ~expected:(m);

  let st = Prover.exec_all ~test:true st
        "Abort.

        abstract f : message->message.
        global lemma _ : equiv(f(if true then diff(n,m) else empty)).
        Proof."
  in
  let st = Prover.exec_command ~test:true "nosimpl cs true." st in
  (* 2 sous-buts: equiv(true, f diff(n,m)) et equiv(true, f empty) *)
  Printer.pr "%a" (Prover.pp_subgoals st) ();

  let terms = get_seq_in_nth_goal st 0 in
  let f = Symbols.Function.of_lsymb (mk "f") (Prover.get_table st) in
  Alcotest.(check' term_testable) 
    ~msg:"equiv(f(if true then diff(n,m) else empty)) →
    true,
    F DIFF(N,M)"
    ~actual:(List.hd terms)
    ~expected:(Term.mk_fun (Prover.get_table st) f  
       [Term.mk_diff [Term.left_proj,n;Term.right_proj,m]]);
  Alcotest.(check' term_testable) 
    ~msg:"equiv(f(if true then diff(n,m) else empty)) →
    TRUE,
    f diff(n,m)"
    ~actual:(List.nth terms 1)
    ~expected:(Term.mk_true);

  let terms = get_seq_in_nth_goal st 1 in
  Alcotest.(check' term_testable) 
    ~msg:"equiv(f(if true then diff(n,m) else empty)) →
    true,
    F EMPTY"
    ~actual:(List.hd terms)
    ~expected:(Term.mk_fun (Prover.get_table st) f  
       [Term.empty]);
  Alcotest.(check' term_testable) 
    ~msg:"equiv(f(if true then diff(n,m) else empty)) →
    TRUE,
    f empty"
    ~actual:(List.nth terms 1)
    ~expected:(Term.mk_true);


  let st = Prover.exec_all ~test:true st
        "Abort.
        global lemma _ : equiv(f(diff(if true then n else empty,if true then m else empty))).
        Proof."
  in
  let st = Prover.exec_command ~test:true "nosimpl cs true." st in
  (* 2 sous-buts: equiv(true, f diff(n,m)) et equiv(true, f empty) *)
  Printer.pr "%a" (Prover.pp_subgoals st) ();

  let f = Symbols.Function.of_lsymb (mk "f") (Prover.get_table st) in
  let terms = get_seq_in_nth_goal st 0 in
  Alcotest.(check' term_testable) 
    ~msg:"equiv(f(diff(if true then n else empty,if true then m else empty)))
    true,
    F DIFF(N,M)"
    ~actual:(List.hd terms)
    ~expected:(Term.mk_fun (Prover.get_table st) f  
       [Term.mk_diff [Term.left_proj,n;Term.right_proj,m]]);
  Alcotest.(check' term_testable) 
    ~msg:"equiv(f(diff(if true then n else empty,if true then m else empty)))
    TRUE,
    f diff(n,m)"
    ~actual:(List.nth terms 1)
    ~expected:(Term.mk_true);

  let terms = get_seq_in_nth_goal st 1 in
  Alcotest.(check' term_testable) 
    ~msg:"equiv(f(diff(if true then n else empty,if true then m else empty)))
    true,
    F EMPTY"
    ~actual:(List.hd terms)
    ~expected:(Term.mk_fun (Prover.get_table st) f  
       [Term.empty]);
  Alcotest.(check' term_testable) 
    ~msg:"equiv(f(diff(if true then n else empty,if true then m else empty)))
    TRUE,
    f empty"
    ~actual:(List.nth terms 1)
    ~expected:(Term.mk_true);

  let st = Prover.exec_all ~test:true st
        "Abort.

        abstract x : message.
        abstract y : message.

        global lemma _ (x,y:message,tau,tau':timestamp) :
          equiv(
            exec@tau, 
            frame@tau, 
            if exec@tau' then x else y, 
            if exec@tau then x else y
          ).
        Proof."
  in
  let st = Prover.exec_command ~test:true "nosimpl cs exec@_." st in
  (* même effet que `cs exec@tau`, `cs exec@tau in 3`, `cs exec@_ in 3`:
      deux buts
      1) exec@tau, exec@tau, frame@tau, if exec@tau' then x else y, x
      2) idem avec y à la fin au lieu de x *)
  Printer.pr "%a" (Prover.pp_subgoals st) ();
  let x = find_in_sys_from_string "x" st in
  let y = find_in_sys_from_string "y" st in

  let terms = get_seq_in_nth_goal st 0 in
  Alcotest.(check' term_testable) 
    ~msg:"global lemma _ (tau,tau':timestamp) :
    equiv(exec@tau, frame@tau, 
      if exec@tau' then x else y, 
      if exec@tau then x else y).
    exec@tau,
    exec@tau,
    frame@tau,
    if exec@tau' then x else y,
    X,
    exec@tau"
    ~actual:(List.nth terms 3)
    ~expected:(x);
  let exectau' = find_in_sys_from_string "exec@tau'" st in
  Alcotest.(check' term_testable) 
    ~msg:"global lemma _ (tau,tau':timestamp) :
    equiv(exec@tau, frame@tau, 
      if exec@tau' then x else y, 
      if exec@tau then x else y).
    exec@tau,
    exec@tau,
    frame@tau,
    IF EXEC@TAU' THEN X ELSE Y,
    x,
    exec@tau"
    ~actual:(List.nth terms 2)
    ~expected:(Term.mk_ite ~simpl:false (exectau') (x) (y));

  let terms = get_seq_in_nth_goal st 1 in
  Alcotest.(check' term_testable) 
    ~msg:"global lemma _ (tau,tau':timestamp) :
    equiv(exec@tau, frame@tau, 
      if exec@tau' then x else y, 
      if exec@tau then x else y).
    exec@tau,
    frame@tau,
    if exec@tau' then x else y,
    Y,
    exec@tau"
    ~actual:(List.nth terms 3)
    ~expected:(y);

  let st = Prover.exec_all ~test:true st
        "Abort.

        global lemma _ (x,y:message,tau,tau':timestamp) :
          equiv(
            exec@tau, 
            frame@tau, 
            if exec@tau' then x else y, 
            if exec@tau then x else y
          ).
        Proof."
  in
  let st = Prover.exec_command ~test:true "nosimpl cs exec@tau." st in
  Printer.pr "%a" (Prover.pp_subgoals st) ();

  let x = find_in_sys_from_string "x" st in
  let y = find_in_sys_from_string "y" st in

  let terms = get_seq_in_nth_goal st 0 in
  Alcotest.(check' term_testable) 
    ~msg:"global lemma _ (tau,tau':timestamp) :
    equiv(
      exec@tau, 
      frame@tau, 
      if exec@tau' then x else y, 
      if exec@tau then x else y
    ).
    exec@tau,
    frame@tau,
    if exec@tau' then x else y,
    X,
    exec@tau"
    ~actual:(List.nth terms 3)
    ~expected:(x);
  let exectau' = find_in_sys_from_string "exec@tau'" st in
  Alcotest.(check' term_testable) 
    ~msg:"global lemma _ (tau,tau':timestamp) :
    equiv(
      exec@tau, 
      frame@tau, 
      if exec@tau' then x else y, 
      if exec@tau then x else y
    ).
    exec@tau,
    frame@tau,
    IF EXEC@TAU' THEN X ELSE Y,
    x,
    exec@tau"
    ~actual:(List.nth terms 2)
    ~expected:(Term.mk_ite ~simpl:false (exectau') (x) (y));

  let terms = get_seq_in_nth_goal st 1 in
  Alcotest.(check' term_testable) 
    ~msg:"global lemma _ (tau,tau':timestamp) :
    equiv(
      exec@tau, 
      frame@tau, 
      if exec@tau' then x else y, 
      if exec@tau then x else y
    ).
    exec@tau,
    frame@tau,
    if exec@tau' then x else y,
    Y,
    exec@tau"
    ~actual:(List.nth terms 3)
    ~expected:(y);
  let exectau' = find_in_sys_from_string "exec@tau'" st in
  Alcotest.(check' term_testable) 
    ~msg:"global lemma _ (tau,tau':timestamp) :
    equiv(
      exec@tau, 
      frame@tau, 
      if exec@tau' then x else y, 
      if exec@tau then x else y
    ).
    exec@tau,
    frame@tau,
    IF EXEC@TAU' THEN X ELSE Y,
    y,
    exec@tau"
    ~actual:(List.nth terms 2)
    ~expected:(Term.mk_ite ~simpl:false (exectau') (x) (y));


  let st = Prover.exec_all ~test:true st
        "Abort.

        global lemma _ (x,y:message,tau,tau':timestamp) :
          equiv(
            exec@tau, 
            frame@tau, 
            if exec@tau' then x else y, 
            if exec@tau then x else y
          ).
        Proof."
  in
  let st = Prover.exec_command ~test:true "nosimpl cs exec@tau in 3." st in
  Printer.pr "%a" (Prover.pp_subgoals st) ();

  let x = find_in_sys_from_string "x" st in
  let y = find_in_sys_from_string "y" st in

  let terms = get_seq_in_nth_goal st 0 in
  Alcotest.(check' term_testable) 
    ~msg:"global lemma _ (tau,tau':timestamp) :
    equiv(
      exec@tau, 
      frame@tau, 
      if exec@tau' then x else y, 
      if exec@tau then x else y
    ). →
    if exec@tau' then x else y,
    frame@tau,
    exec@tau,
    exec@tau,
    X"
    ~actual:(List.nth terms 4)
    ~expected:(x);

  let terms = get_seq_in_nth_goal st 1 in
  Alcotest.(check' term_testable) 
    ~msg:"global lemma _ (tau,tau':timestamp) :
    equiv(
      exec@tau, 
      frame@tau, 
      if exec@tau' then x else y, 
      if exec@tau then x else y
    ). →
    if exec@tau' then x else y,
    frame@tau,
    exec@tau,
    exec@tau,
    Y"
    ~actual:(List.nth terms 4)
    ~expected:(y);


  let st = Prover.exec_all ~test:true st
        "Abort.

        global lemma _ (x,y:message,tau,tau':timestamp) :
          equiv(
            exec@tau, 
            frame@tau, 
            if exec@tau' then x else y, 
            if exec@tau then x else y
          ).
        Proof."
  in
  let st = Prover.exec_command ~test:true "nosimpl cs exec@_ in 3." st in
  Printer.pr "%a" (Prover.pp_subgoals st) ();

  let x = find_in_sys_from_string "x" st in
  let y = find_in_sys_from_string "y" st in

  let terms = get_seq_in_nth_goal st 0 in
  Alcotest.(check' term_testable) 
    ~msg:"global lemma _ (tau,tau':timestamp) :
    equiv(
      exec@tau, 
      frame@tau, 
      if exec@tau' then x else y, 
      if exec@tau then x else y
    ).
    if exec@tau' then x else y,
    frame@tau,
    exec@tau,
    exec@tau,
    X"
    ~actual:(List.nth terms 4)
    ~expected:(x);

  let terms = get_seq_in_nth_goal st 1 in
  Alcotest.(check' term_testable) 
    ~msg:"global lemma _ (tau,tau':timestamp) :
    equiv(
      exec@tau, 
      frame@tau, 
      if exec@tau' then x else y, 
      if exec@tau then x else y
    ).
    if exec@tau' then x else y,
    frame@tau,
    exec@tau,
    exec@tau,
    Y"
    ~actual:(List.nth terms 4)
    ~expected:(y)

let namelength () =
  let mk c = L.mk_loc L._dummy c in      
  let st = Prover.exec_all ~test:true (Prover.init ~withPrelude:false ())
        "
        system null.
        name n : message.
        name m : message.

        lemma _ : true.
        Proof.
        " in
  Printer.pr "%a@." (Prover.pp_subgoals st) ();
  let tn = find_in_sys_from_string "n" st in
  let _tm = find_in_sys_from_string "m" st in
  let tyn = Term.ty tn in 
  let table = Prover.get_table st in

  let axiom_n = "namelength_n" in
  let axiom_m = "namelength_m" in

  let stmt_n = Lemma.find_stmt_local (mk axiom_n) table in
  let stmt_m = Lemma.find_stmt_local (mk axiom_m) table in

  let system = SystemExpr.context_any in

  Alcotest.(check (sys_testable table)) 
    "SystemExpr equals → context_any"
    (system.set)
    (stmt_n.system.set);
  
  (* Should be of same length ↓ *)
  Printer.pr "Term n: %a@." Term.pp stmt_n.formula;
  Printer.pr "Term m: %a@." Term.pp stmt_m.formula;

  let n = Symbols.Name.of_lsymb (mk "n") table in
  let tn = Term.mk_name (Term.mk_symb n tyn) [] in
  
  let cst = Type.to_string tyn in
  let name_hash = "namelength_" ^ cst in
  let lsy = L.mk_loc L._dummy (name_hash) in

  let table, fname = match Symbols.Function.of_lsymb_opt lsy table with
    | Some fn -> table, fn
    | None -> assert false
  in
  let cst = Term.mk_fun table fname [] in
  let f = Term.mk_eq (Term.mk_len tn) cst in

  Alcotest.(check (term_testable)) 
    "axiom namelength_n → len(n) = namelength_message"
    (f)
    (stmt_n.formula);

  let _ = match stmt_m.formula, stmt_n.formula with
  | Term.App (Fun (sy ,_),[_t1;t2]),
    Term.App (Fun (sy',_),[_t1';t2'])
    when sy = Symbols.fs_eq && sy' = Symbols.fs_eq -> 
    Alcotest.(check (term_testable)) 
      "len(n) = namelength_message = len(m) "
      (t2)
      (t2');
  | _ -> assert false
  in ()

let namelength2 () =
  let mk c = L.mk_loc L._dummy c in      
  let st = Prover.exec_all ~test:true (Prover.init ~withPrelude:false ())
        "
        system null.
        name n : message * message.

        lemma _ : True.
        Proof.
        " in
  Printer.pr "%a@." (Prover.pp_subgoals st) ();
  let tn = find_in_sys_from_string "n" st in
  let tyn = Term.ty tn in 
  let table = Prover.get_table st in

  let axiom_n = "namelength_n" in

  let stmt_n = Lemma.find_stmt_local (mk axiom_n) table in

  let system = SystemExpr.context_any in

  Alcotest.(check (sys_testable table)) 
    "SystemExpr equals → context_any"
    (system.set)
    (stmt_n.system.set);
  
  (* Should be of same length ↓ *)
  Printer.pr "Term n: %a@." Term.pp stmt_n.formula;

  let n = Symbols.Name.of_lsymb (mk "n") table in
  let tn = Term.mk_name (Term.mk_symb n tyn) [] in
  
  let cst = Type.to_string tyn in
  let name_hash = "namelength_" ^ cst in
  let lsy = L.mk_loc L._dummy (name_hash) in

  let table, fname = match Symbols.Function.of_lsymb_opt lsy table with
    | Some fn -> table, fn
    | None -> assert false
  in
  let cst = Term.mk_fun table fname [] in
  let f = Term.mk_atom `Eq (Term.mk_len tn) (cst) in

  Alcotest.(check (term_testable)) 
    "axiom namelength_n → len(n) = namelength_message•message"
    (f)
    (stmt_n.formula)

let tests =
  [ ("case_study", `Quick, Util.catch_error case_study) ;
    ("namelength", `Quick, Util.catch_error namelength);
    ("namelength2", `Quick, Util.catch_error namelength2);
    ("case_study_fail", `Quick, Util.catch_error case_study_fail) ;
    ("case_study_fail'", `Quick, Util.catch_error case_study_fail') ]
