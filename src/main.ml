
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
  lexbuf := some @@ Lexing.from_channel (Pervasives.open_in fname);
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

let rec main_loop ~test ?(save=true) mode =
  if !interactive then Printer.prt `Prompt "";
  (* Initialize definitions before parsing system description.
   * TODO this is not doable anymore (with refactoring this code)
   * concerning definitions of functions, names, ... symbols;
   * it should not matter if we do not undo the initial definitions *)
  if mode = InputDescr then begin
    Process.reset ();
    Prover.reset ();
    Symbols.restore_builtin ()
  end else
    (* Otherwise save the state if instructed to do so.
     * In practice we save except after errors. *)
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
    (* If the command is an undo, we catch it only if we are not waiting for
       a system description. *)
    | mode, ParsedUndo nb_undo when mode <> InputDescr ->
      begin
        let new_mode = reset_state nb_undo in
        begin match new_mode with
          | ProofMode -> Printer.pr "%a" pp_goal ()
          | GoalMode -> Printer.pr "%a" Action.pp_actions ()
          | InputDescr | WaitQed -> ()
        end ;
        main_loop ~test new_mode
      end

    | InputDescr, ParsedInputDescr ->
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

    | GoalMode, ParsedInputDescr ->
      Printer.pr "%a" Action.pp_actions ();
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
          add_new_goal (i,f);
          Printer.pr "@[<v 2>Goal %s :@;@[%a@]@]@."
            i
            Prover.Goal.pp_init f;
          main_loop ~test GoalMode
      end

    | GoalMode, EOF -> Printer.pr "Goodbye!@." ; if not test then exit 0

    | _, ParsedQed ->
        if test then raise @@ Failure "unfinished" else
          error ~test mode "Unexpected command."

    | _, _ -> error ~test mode "Unexpected command."

and error ~test mode s =
  Printer.prt `Error "%s" s;
  if !interactive then main_loop ~test ~save:false mode else
  if not test then exit 1

let main_loop ?(test=false) ?save mode = main_loop ~test ?save mode

let interactive_prover () =
  Printer.prt `Start "MetaBC interactive mode.";
  Printer.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
  try main_loop InputDescr
  with End_of_file -> Printer.prt `Error "End of file, exiting."

let run ?(test=false) filename =
  (* TODO: I am forcing the usage of ANSI escape sequence. We probably want an
     option to remove it. *)
  if test then Printer.printer_mode := Printer.Test;
  Printer.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
  setup_lexbuf filename;
  main_loop ~test InputDescr

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
    "Substitution", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure Tactics.NotEqualArguments)
        (fun () -> run ~test "tests/alcotest/substitution.mbc")
    end ;
    "Collision", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure Tactics.NoSSC)
        (fun () -> run ~test "tests/alcotest/collisions.mbc")
    end ;
    "Exists Intro", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure (Tactics.Undefined "a1"))
        (fun () -> run ~test "tests/alcotest/existsintro_fail.mbc")
    end ;
    "Vars not eq", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/vars_not_eq.mbc")
    end ;
    "TS not leq", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/ts_leq_not_lt.mbc")
    end ;
    "Euf Mvar", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure Bad_SSC)
        (fun () -> run ~test "tests/alcotest/euf_mvar.mbc")
    end ;
    "Euf Bad SSC 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure Bad_SSC)
        (fun () -> run ~test "tests/alcotest/eufnull.mbc")
    end ;
    "Euf Bad SSC 2", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure Bad_SSC)
        (fun () -> run ~test "tests/alcotest/euf_deep.mbc")
    end ;
    "Euf Bad SSC 3", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure Bad_SSC)
        (fun () -> run ~test "tests/alcotest/euf_cond.mbc")
    end ;
    "Euf collect in key position", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/euf_deepkey.mbc")
    end ;
    "Euf collect indirect bound variables", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/euf_bv.mbc")
    end ;
    "Euf collect direct bound variables", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/euf_bv_direct.mbc")
    end ;
    "Euf environment", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactics.(Tactic_soft_failure
                    (Cannot_convert (Theory.(Undefined "i1")))))
        (fun () -> run ~test "tests/alcotest/euf_env.mbc")
    end ;
    "Sign Bad SSC", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure Bad_SSC)
        (fun () -> run ~test "tests/alcotest/sign.mbc")
    end ;
    "Axiom Systems", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_hard_failure NoAssumpSystem)
        (fun () -> run ~test "tests/alcotest/axiom1.mbc")
    end ;
    "Axiom Systems", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_hard_failure NoAssumpSystem)
        (fun () -> run ~test "tests/alcotest/axiom2.mbc")
    end ;
    "Substitution no capture", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/capture.mbc")
    end ;
    "Not Depends", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure (Tactics.NotDepends ("A1(i)","A1(i)")))
        (fun () -> run ~test "tests/alcotest/depends.mbc")
    end ;
    "Fresh Not Ground", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure
          (Tactics.Failure "can only be applied on ground terms"))
        (fun () -> run ~test "tests/alcotest/fresh_reach_var.mbc")
    end ;
    "Check equalities false if unsupported terms", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/completion_unsupported_term.mbc")
    end ;
  ] ;
  Parserbuf.add_suite_restore "Equivalence" [
    "Refl", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure (Tactics.Failure "Frames not identical"))
        (fun () -> run ~test "tests/alcotest/neqrefl.mbc")
    end ;
    "Fresh Frame", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/fresh_frame.mbc")
    end ;
    "Fresh System", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/fresh_system.mbc")
    end ;
    "Make biterm", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/fresh_system.mbc")
    end ;
    "DDH", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure Tactics.NotDDHContext)
        (fun () -> run ~test "tests/alcotest/ddh.mbc")
    end ;
    "DDH2", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure Tactics.NotDDHContext)
        (fun () -> run ~test "tests/alcotest/ddh.mbc")
    end ;
    "FA Dup", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/equivalent.mbc")
    end ;
    "XOR", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/xor.mbc")
    end ;
    "Indexed abstract", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Tactic_soft_failure
           (Tactics.Failure "cannot automatically prove goal"))
        (fun () -> run ~test "tests/alcotest/idx_abs.mbc")
    end ;
    "Indexed collision", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/idx_collision.mbc")
    end ;
    "Indexed EUF", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "unfinished")
        (fun () -> run ~test "tests/alcotest/idx_euf.mbc")
    end ;
  ]
