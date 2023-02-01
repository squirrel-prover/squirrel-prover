open Squirrellib
module ES = EquivSequent
module L = Location
(* module ProverLib = Squirrellib.ProverLib *)

let pprint_option ppf = function 
  | Some s -> Fmt.pf ppf "%s" s
  | None -> Fmt.pf ppf ""

let string_testable = Alcotest.testable pprint_option (=)

let term_testable = Alcotest.testable (Term.pp_dbg) (Term.equal)

let case_study () =

  let get_nth_equiv_terms st i = 
    let subgoals = Prover.get_subgoals st in
    let g = List.nth subgoals i in
    match g with
    | Equiv j -> ES.goal_as_equiv j
    | _ -> assert false
  in

  let mkvar x s = Term.mk_var (snd (Vars.make `Approx Vars.empty_env s x)) in

  let st = Prover.init () in
  (* let st = Prover.set_param st (C.s_post_quantum, (Co.Param_bool true)) in *)
  let st = 
    Prover.exec_all st
        "mutable state : message = empty.
        name nfresh : message.
        system null.

        global goal _ : equiv(if true then zero else empty).
        Proof."
  in
  (* Attention, simpl va trivialiser ce but. *)
  let st = Prover.exec_command "nosimpl cs true." st in
  Printer.pr "%a" (Prover.pp_subgoals st) ();
  let terms = get_nth_equiv_terms st 0 in
  Alcotest.(check term_testable) 
    "if true then zero else empty → TRUE,zero"
    (List.hd terms)
    (Term.mk_true);
  Alcotest.(check term_testable) 
    "if true then zero else empty → true,ZERO"
    (List.nth terms 1)
    (Term.mk_zero);

  let terms = get_nth_equiv_terms st 1 in
  Alcotest.(check term_testable) 
    "if true then zero else empty → TRUE,empty"
    (List.hd terms)
    (Term.mk_true);
  Alcotest.(check term_testable) 
    "if true then zero else empty → true,EMPTY"
    (List.nth terms 1)
    (Term.empty);

  (* deux sous-buts, l'un avec true,zero, l'autre true,empty *)
  let st = Prover.exec_all st
        "Abort.

        name n : message.
        name m : message.

        global goal _ : equiv(if true then zero else empty, if true then n else m).
        Proof."
  in
  (* Attention, simpl va trivialiser ce but. *)
  let st = Prover.exec_command "nosimpl cs true." st in
  Printer.pr "%a" (Prover.pp_subgoals st) ();
  (* deux sous-buts, l'un avec equiv(true,zero,n) l'autre equiv(true,empty,m) *)
  let terms = get_nth_equiv_terms st 0 in
  Alcotest.(check term_testable) 
    "equiv(if true then zero else empty, if true then n else m) → TRUE,zero,n"
    (List.hd terms)
    (Term.mk_true);
  Alcotest.(check term_testable) 
    "equiv(if true then zero else empty, if true then n else m) → true,ZERO,n"
    (List.nth terms 1)
    (Term.mk_zero);
  (* FIXME *)
  let _n = mkvar "n" Type.Message in
  (* Alcotest.(check term_testable) *) 
  (*   "if true then zero else empty → true,zero,N" *)
  (*   (List.nth terms 2) *)
  (*   (n); *)

  let terms = get_nth_equiv_terms st 1 in
  Alcotest.(check term_testable) 
    "equiv(if true then zero else empty, if true then n else m) →
    TRUE,empty,m"
    (List.hd terms)
    (Term.mk_true);
  Alcotest.(check term_testable) 
    "equiv(if true then zero else empty, if true then n else m) →
    true,EMPTY,m"
    (List.nth terms 1)
    (Term.empty);
  (* FIXME *)
  (* let m = mkvar "m" Type.Message in *)
  (* Alcotest.(check term_testable) *) 
  (*   "if true then zero else empty → true,empty,M" *)
  (*   (List.nth terms 2) *)
  (*   (m); *)

  let st = Prover.exec_all st
        "Abort.

        global goal _ : equiv(
                        if true then zero else empty, 
                        if true then n else m
                        ).
        Proof."
  in
  (* Attention, simpl va trivialiser ce but. *)
  let st = Prover.exec_command "nosimpl cs true in 1." st in
  Printer.pr "%a" (Prover.pp_subgoals st) ();
  (* deux sous-buts, equiv(true,if true then zero else empty,n)
     et  equiv(true,if true then zero else empty,m) *)
  let terms = get_nth_equiv_terms st 0 in
  Alcotest.(check term_testable) 
    "equiv(if true then zero else empty, if true then n else m) → 
    TRUE,
    if true then zero else empty,
    n"
    (List.hd terms)
    (Term.mk_true);
  Alcotest.(check term_testable) 
    "equiv(if true then zero else empty, if true then n else m) → 
    true,
    IF TRUE THEN ZERO ELSE EMPTY,
    n"
    (List.nth terms 1)
    (Term.mk_ite ~simpl:false (Term.mk_true) (Term.mk_zero) (Term.empty));
  (* FIXME *)
  (* let n = mkvar "n" Type.Message in *)
  (* Alcotest.(check term_testable) *) 
  (*   "if true then zero else empty → true,empty,N" *)
  (*   (List.nth terms 2) *)
  (*   (n); *)

  let terms = get_nth_equiv_terms st 1 in
  Alcotest.(check term_testable) 
    "equiv(if true then zero else empty, if true then n else m) → 
    TRUE,
    if true then zero else empty,
    m"
    (List.hd terms)
    (Term.mk_true);
  Alcotest.(check term_testable) 
    "equiv(if true then zero else empty, if true then n else m) → 
    true,
    IF TRUE THEN ZERO ELSE EMPTY,
    m"
    (List.nth terms 1)
    (Term.mk_ite ~simpl:false (Term.mk_true) (Term.mk_zero) (Term.empty));
  (* FIXME *)
  (* let m = mkvar "m" Type.Message in *)
  (* Alcotest.(check term_testable) *) 
    (* "equiv(if true then zero else empty, if true then n else m) → *) 
    (* true, *)
    (* if true then zero else empty, *)
    (* M" *)
  (*   (List.nth terms 2) *)
  (*   (m); *)

  let st = Prover.exec_all st
        "Abort.

        abstract f : message->message.
        global goal _ : equiv(f(if true then diff(n,m) else empty)).
        Proof."
  in
  let st = Prover.exec_command "nosimpl cs true." st in
  (* 2 sous-buts: equiv(true, f diff(n,m)) et equiv(true, f empty) *)
  Printer.pr "%a" (Prover.pp_subgoals st) ();

  let st = Prover.exec_all st
        "Abort.
        global goal _ : equiv(f(diff(if true then n else empty,if true then m else empty))).
        Proof."
  in
  let st = Prover.exec_command "nosimpl cs true." st in
  (* 2 sous-buts: equiv(true, f diff(n,m)) et equiv(true, f empty) *)
  Printer.pr "%a" (Prover.pp_subgoals st) ();

  let st = Prover.exec_all st
        "Abort.

        global goal _ (x,y:message,tau,tau':timestamp) :
          equiv(exec@tau, frame@tau, if exec@tau' then x else y, if exec@tau then x else y).
        Proof."
  in
  let st = Prover.exec_command "nosimpl cs exec@_." st in
  (* même effet que `cs exec@tau`, `cs exec@tau in 3`, `cs exec@_ in 3`:
      deux buts
      1) exec@tau, exec@tau, frame@tau, if exec@tau' then x else y, x
      2) idem avec y à la fin au lieu de x *)
  Printer.pr "%a" (Prover.pp_subgoals st) ();

  let st = Prover.exec_all st
        "Abort.

        global goal _ (x,y:message,tau,tau':timestamp) :
          equiv(exec@tau, frame@tau, if exec@tau' then x else y, if exec@tau then x else y).
        Proof."
  in
  let st = Prover.exec_command "nosimpl cs exec@tau." st in
  Printer.pr "%a" (Prover.pp_subgoals st) ();

  let st = Prover.exec_all st
        "Abort.

        global goal _ (x,y:message,tau,tau':timestamp) :
          equiv(exec@tau, frame@tau, if exec@tau' then x else y, if exec@tau then x else y).
        Proof."
  in
  let st = Prover.exec_command "nosimpl cs exec@tau in 3." st in
  Printer.pr "%a" (Prover.pp_subgoals st) ();

  let st = Prover.exec_all st
        "Abort.

        global goal _ (x,y:message,tau,tau':timestamp) :
          equiv(exec@tau, frame@tau, if exec@tau' then x else y, if exec@tau then x else y).
        Proof."
  in
  let st = Prover.exec_command "nosimpl cs exec@_ in 3." st in
  Printer.pr "%a" (Prover.pp_subgoals st) ();

  let _st = Prover.exec_command "Abort." st in
  ()

let tests = [ ("case_study", `Quick, case_study);
            ]
