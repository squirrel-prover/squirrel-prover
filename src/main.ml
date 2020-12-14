
open Utils

module Initialization = struct
  (* Opening these modules is only useful for their side effects,
   * e.g. registering tactics. *)
  open TraceTactics
  open EquivTactics
end

let usage = Printer.strf "Usage: %s filename" (Filename.basename Sys.argv.(0))

let args  = ref []
let verbose = ref false
let interactive = ref false

let speclist = [
  ("-i", Arg.Set interactive, "interactive mode (e.g, for proof general)");
  ("-v", Arg.Set verbose, "display more informations");
]

(** Lexbuf used in non-interactive mode. *)
let lexbuf : Lexing.lexbuf option ref = ref None
let filename = ref "No file opened"

let setup_lexbuf fname =
  lexbuf := some @@ Lexing.from_channel (Stdlib.open_in fname);
  filename := fname;;

(** [parse_next parser_fun] parse the next line of the input (or a filename)
    according to the given parsing function [parser_fun]. Used in interactive
    mode, depending on what is the type of the next expected input. *)
let parse_next parser_fun =
  if !interactive then
    parser_fun (Lexing.from_channel stdin) "new input"
  else
    parser_fun (Utils.opt_get !lexbuf) !filename

open Prover
open Tactics

(** The main loop of the prover. The mode defines in what state the prover is,
    e.g is it waiting for a proof script, or a system description, etc.
    [save] allows to specify is the current state must be saved, so that
    one can backtrack.
*)
let rec main_loop ~test ?(save=true) mode =
  if !interactive then Printer.prt `Prompt "";
  (* Save the state if instructed to do so.
   * In practice we save except after errors and the first call. *)
  if save then save_state mode ;
  match
    let parse_buf =
      Parserbuf.parse_from_buf
        ~test ~interactive:!interactive
        Parser.interactive
    in
    mode, parse_next parse_buf
  with
    | exception (Parserbuf.Error s) -> error ~test mode s
    | exception (Prover.ParseError s) -> error ~test mode s
    | mode, ParsedUndo nb_undo ->
      begin
        let new_mode = reset_state nb_undo in
        begin match new_mode with
          | ProofMode -> Printer.pr "%a" pp_goal ()
          | GoalMode -> Printer.pr "%a" Action.pp_actions ()
          | WaitQed -> ()
        end ;
        main_loop ~test new_mode
      end

    | GoalMode, ParsedInputDescr decls ->
      Decl.declare_list decls;
      Printer.pr "%a" Action.pp_actions ();
      main_loop ~test GoalMode

    | ProofMode, ParsedTactic utac ->
      if not !interactive then
        Printer.prt `Prompt "%a" Prover.pp_ast utac ;
      begin match eval_tactic utac with
      | true ->
          Printer.prt `Goal "Goal %s is proved"
            (match Prover.current_goal () with
               | Some (i, _) -> i
               | None -> assert false);
          complete_proof ();
          main_loop ~test WaitQed
      | false ->
          Printer.pr "%a" pp_goal ();
          main_loop ~test ProofMode
      | exception (Tactic_soft_failure s) when not test ->
          let s = Printer.strf "%a" Tactics.pp_tac_error s in
          error ~test ProofMode ("Tactic failed: " ^ s ^ ".")
      | exception (Tactic_hard_failure s) when not test ->
          let s = Printer.strf "%a" Tactics.pp_tac_error s in
          error ~test ProofMode
            ("Tactic ill-formed or unapplicable: " ^ s ^ ".")
      end

    | WaitQed, ParsedQed ->
      Printer.prt `Result "Exiting proof mode.@.";
      main_loop ~test GoalMode

    | GoalMode, ParsedSetOption sp ->
      Config.set_param sp;
      main_loop ~test GoalMode

    | GoalMode, ParsedGoal goal ->
      begin
        match goal with
        | Prover.Gm_proof ->
          begin
            match start_proof () with
            | None ->
              Printer.pr "%a" pp_goal ();
              main_loop ~test ProofMode
            | Some es -> error ~test GoalMode es
          end
        | Prover.Gm_goal (i,f) ->
          (try
            add_new_goal (i,f)
          with  (Prover.ParseError s) -> error ~test mode s);
          Printer.pr "@[<v 2>Goal %s :@;@[%a@]@]@."
            i
            Prover.Goal.pp_init f;
          main_loop ~test GoalMode
      end

    | GoalMode, EOF -> Printer.pr "Goodbye!@." ; if not test then exit 0

    | WaitQed, ParsedAbort ->
        if test then raise @@ Failure "Trying to abort a completed proof." else
          error ~test mode "Trying to abort a completed proof."

    | ProofMode, ParsedAbort ->
      Printer.prt `Result "Exiting proof mode and aborting current proof.@.";
      Prover.reset ();
      main_loop ~test GoalMode

    | _, ParsedQed ->
        if test then raise @@ Failure "unfinished" else
          error ~test mode "Unexpected command."

    | _, _ -> error ~test mode "Unexpected command."

and error ~test mode s =
  Printer.prt `Error "%s" s;
  if !interactive then main_loop ~test ~save:false mode else
  if not test then exit 1

let start_main_loop ?(test=false) () = 
  (* Initialize definitions before parsing system description.
   * TODO this is not doable anymore (with refactoring this code)
   * concerning definitions of functions, names, ... symbols;
   * it should not matter if we do not undo the initial definitions *)
  Process.reset ();
  Prover.reset ();
  Symbols.restore_builtin ();
  main_loop ~test GoalMode

let interactive_prover () =
  Printer.prt `Start "Squirrel Prover interactive mode.";
  Printer.prt `Start "Git commit: %s" Commit.hash_commit;
  Printer.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
  try start_main_loop ()
  with End_of_file -> Printer.prt `Error "End of file, exiting."

let run ?(test=false) filename =
  (* TODO: I am forcing the usage of ANSI escape sequence. We probably want an
     option to remove it. *)
  if test then Printer.printer_mode := Printer.Test;
  Printer.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
  setup_lexbuf filename;
  start_main_loop ~test ()

let main () =
  let collect arg = args := !args @ [arg] in
  let _ = Arg.parse speclist collect usage in
  if List.length !args = 0 && not !interactive then
    Arg.usage speclist usage
  else if List.length !args > 0 && !interactive then
    Printer.pr "No file arguments accepted when running in interactive mode.@."
  else if !interactive then
    interactive_prover ()
  else
    let filename = List.hd !args in
    run filename

let () =
  let test = true in
  Parserbuf.add_suite_restore "Tactics" [
    "Exists Intro", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure (Tactics.Undefined "a1"))
        (fun () -> run ~test "tests/alcotest/existsintro_fail.sp")
    end ;
    "Vars not eq", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/vars_not_eq.sp")
    end ;
    "TS not leq", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/ts_leq_not_lt.sp")
    end ;
    "SEnc Bad SSC - INCTXT 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure SEncNoRandom)
        (fun () -> run ~test "tests/alcotest/intctxt_nornd.sp")
    end ;
    "SEnc Bad SSC - INTCTXT 2", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure SEncRandomNotFresh)
        (fun () -> run ~test "tests/alcotest/intctxt_rndnotfresh.sp")
    end ;
    "Senc Bad SSC - INTCTXT 3", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure SEncSharedRandom)
        (fun () -> run ~test "tests/alcotest/intctxt_sharedrnd.sp")
    end ;
    "Senc Bad SSC - INTCTXT 4", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure SEncSharedRandom)
        (fun () -> run ~test "tests/alcotest/intctxt_sharedrndind.sp")
    end ;
    "Senc Bad SSC - CCA 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure SEncSharedRandom)
        (fun () -> run ~test "tests/alcotest/cca_sharedrnd.sp")
    end ;
    "Senc Bad SSC - CCA 2", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure SEncSharedRandom)
        (fun () -> run ~test "tests/alcotest/cca_sharedrndframe.sp")
    end ;
    "Senc Bad SSC - CCA 3", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure SEncNoRandom)
        (fun () -> run ~test "tests/alcotest/cca_nornd.sp")
    end ;
    "Senc Bad SSC - ENCKP 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure SEncNoRandom)
        (fun () -> run ~test "tests/alcotest/enckp_nornd.sp")
    end ;
    "Senc Bad SSC - ENCKP 2", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure SEncSharedRandom)
        (fun () -> run ~test "tests/alcotest/enckp_sharedrnd.sp")
    end ;
    "Senc Bad SSC - ENCKP 3", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure SEncSharedRandom)
        (fun () -> run ~test "tests/alcotest/enckp_sharedrndframe.sp")
    end ;
    "Senc Bad SSC - ENCKP 4", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/enckp_dec.sp")
    end ;
    "Axiom Systems", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_hard_failure NoAssumpSystem)
        (fun () -> run ~test "tests/alcotest/axiom2.sp")
    end ;
    "Substitution no capture", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/capture.sp")
    end ;
    "Not Depends", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure (Tactics.NotDepends ("A1(i)","A1(i)")))
        (fun () -> run ~test "tests/alcotest/depends.sp")
    end ;
    "Fresh Not Ground", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure
          (Tactics.Failure "can only be applied on ground terms"))
        (fun () -> run ~test "tests/alcotest/fresh_reach_var.sp")
    end ;
    "Check equalities false if unsupported terms", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/completion_unsupported_term.sp")
    end ;
    "Indexed abstract", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure
           (Tactics.Failure "cannot automatically prove goal"))
        (fun () -> run ~test "tests/alcotest/idx_abs.sp")
    end ;
    "Indexed collision", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/idx_collision.sp")
    end ;
    "Find equality", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure (Failure "Equations satisfiable"))
        (fun () -> run ~test "tests/alcotest/try.sp")
    end ;
    "Undo does not maintain old truth", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/undo.sp")
    end ;
  ] ;
  Parserbuf.add_suite_restore "Equivalence" [
    "Fresh Frame", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/fresh_frame.sp")
    end ;
    "Fresh System", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/fresh_system.sp")
    end ;
    "Make biterm", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/fresh_system.sp")
    end ;
    "DDH", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure Tactics.NotDDHContext)
        (fun () -> run ~test "tests/alcotest/ddh.sp")
    end ;
    "DDH2", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure Tactics.NotDDHContext)
        (fun () -> run ~test "tests/alcotest/ddh.sp")
    end ;
    "FA Dup Input", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure (Tactics.NoReflMacros))
        (fun () -> run ~test "tests/alcotest/fadup_input.sp")
    end ;
    "XOR", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/xor.sp")
    end ;
    "XOR2", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure
           (Failure "name is not XORed on both sides"))
        (fun () -> run ~test "tests/alcotest/xor2.sp")
    end ;
    "Not XOR", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure
           (Failure
              "Can only apply xor tactic on terms of the form u XOR v"))
        (fun () -> run ~test "tests/alcotest/notxor.sp")
    end ;
    "Pred Init", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/pred.sp")
    end ;
    "Pred not injective", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/pred2.sp")
    end ;
    "ENC-KP ground", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure Bad_SSC)
        (fun () -> run ~test "tests/alcotest/enckp_ground.sp")
    end ;
    "ENC-KP freshness wrt frame", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/enckp_fresh.sp")
    end ;
    "ENC-KP freshness wrt context", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/enckp_fresh_ctxt.sp")
    end ;
    "ENC-KP key usability wrt frame", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure Bad_SSC)
        (fun () -> run ~test "tests/alcotest/enckp_key.sp")
    end ;
    "ENC-KP key usability wrt context", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure Bad_SSC)
        (fun () -> run ~test "tests/alcotest/enckp_key_ctxt.sp")
    end ;
  ]
