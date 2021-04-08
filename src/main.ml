open Utils

module L = Location

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
    parser_fun (Utils.oget !lexbuf) !filename

(*------------------------------------------------------------------*)
(** Print precise location error (to be caught by emacs) *)
let pp_loc_error ppf loc =
  if !interactive then
    let lexbuf = Lexing.from_channel stdin in
    (* Not sure startpos does anything *)
    let startpos = lexbuf.Lexing.lex_curr_p.pos_cnum in
    Fmt.pf ppf
      "[error-%d-%d]"
      (max 0 (loc.L.loc_bchar - startpos))
      (max 0 (loc.L.loc_echar - startpos))

let pp_loc_error_opt ppf = function
  | None -> ()
  | Some l -> pp_loc_error ppf l

type cmd_error = 
  | Unexpected_command 
  | StartProofError of string
  | AbortIncompleteProof

exception Cmd_error of cmd_error

let pp_cmd_error fmt = function
  | Unexpected_command -> Fmt.pf fmt "Unexpected command."
  | StartProofError s -> Fmt.pf fmt "%s" s
  | AbortIncompleteProof -> Fmt.pf fmt "Trying to abort a completed proof."

let cmd_error e = raise (Cmd_error e)


(*------------------------------------------------------------------*)
open Tactics

exception Unfinished 

(* State of the main loop.
   TODO: include everything currently handled statefully in Prover.ml *)
type loop_state = { mode : Prover.prover_mode;
                    table : Symbols.table; }

(** The main loop body. *)
let main_loop_body ~test state =
  match
    let parse_buf =
      Parserbuf.parse_from_buf
        ~test ~interactive:!interactive
        Parser.interactive
    in
    state.mode, parse_next parse_buf
  with
    | mode, ParsedUndo nb_undo ->
      let new_mode, new_table = Prover.reset_state nb_undo in
      let () = match new_mode with
        | ProofMode -> Printer.pr "%a" Prover.pp_goal ()
        | GoalMode -> Printer.pr "%a" Action.pp_actions new_table
        | WaitQed -> ()
        | AllDone -> assert false in
      { mode = new_mode; table = new_table; }

    | GoalMode, ParsedInputDescr decls ->
      let table = Prover.declare_list state.table decls in
      Printer.pr "%a" System.pp_systems table;
      { mode = GoalMode; table = table; }

    | ProofMode, ParsedTactic utac ->
      if not !interactive then
        Printer.prt `Prompt "%a" Prover.pp_ast utac ;
      begin match Prover.eval_tactic utac with
      | true ->
          Printer.prt `Goal "Goal %s is proved"
            (match Prover.current_goal () with
               | Some (i, _) -> i
               | None -> assert false);
          Prover.complete_proof ();
          { state with mode = WaitQed }
      | false ->
          Printer.pr "%a" Prover.pp_goal ();
          { state with mode = ProofMode }
      end

    | WaitQed, ParsedQed ->
      Printer.prt `Result "Exiting proof mode.@.";
      { state with mode = GoalMode }

    | GoalMode, ParsedSetOption sp ->
      Config.set_param sp;
      { state with mode = GoalMode }

    | GoalMode, ParsedGoal goal ->
      begin
        match L.unloc goal with
        | Prover.Gm_proof ->
          begin
            match Prover.start_proof () with
            | None ->
              Printer.pr "%a" Prover.pp_goal ();
              { state with mode = ProofMode }
            | Some es -> cmd_error (StartProofError es)
          end
        | Prover.Gm_goal (i,f) ->
          let i,f = Prover.declare_new_goal state.table (L.loc goal) i f in
          Printer.pr "@[<v 2>Goal %s :@;@[%a@]@]@."
            i
            Prover.Goal.pp_init f;
          { state with mode = GoalMode; }
      end

    | GoalMode, EOF -> { state with mode = AllDone; }

    | WaitQed, ParsedAbort ->
      if test then raise @@ Failure "Trying to abort a completed proof." else
        cmd_error AbortIncompleteProof

    | ProofMode, ParsedAbort ->
      Printer.prt `Result "Exiting proof mode and aborting current proof.@.";
      Prover.abort ();
      { state with mode = GoalMode; }

    | _, ParsedQed ->
      if test then raise Unfinished else 
        cmd_error Unexpected_command

    | _, _ -> cmd_error Unexpected_command


(** The main loop of the prover. The mode defines in what state the prover is,
    e.g is it waiting for a proof script, or a system description, etc.
    [save] allows to specify is the current state must be saved, so that
    one can backtrack.
*)
let rec main_loop ~test ?(save=true) state =
  if !interactive then Printer.prt `Prompt "";
  (* Save the state if instructed to do so.
   * In practice we save except after errors and the first call. *)
  if save then Prover.save_state state.mode state.table ;

  match
    let new_state = main_loop_body ~test state in
    new_state, new_state.mode with
  (* exit prover *)
  | _, AllDone -> Printer.pr "Goodbye!@." ; if not test then exit 0

  (* loop *)
  | new_state, _ -> (main_loop[@tailrec]) ~test new_state

  (* exception handling *)
  | exception (Parserbuf.Error s) -> 
    error ~test state (fun fmt -> Fmt.string fmt s)
      
  | exception (Prover.ParseError s) -> 
    error ~test state (fun fmt -> Fmt.string fmt s)
      
  | exception (Cmd_error e) ->
    error ~test state (fun fmt -> pp_cmd_error fmt e)

  | exception (Process.ProcError e) ->
    error ~test state (fun fmt -> Process.pp_proc_error pp_loc_error fmt e)

  | exception (Prover.Decl_error e) when not test ->
    error ~test state (fun fmt -> Prover.pp_decl_error pp_loc_error fmt e)
      
  | exception (Theory.Conv e) when not test ->
    error ~test state (fun fmt -> Theory.pp_error pp_loc_error fmt e)
      
  | exception (Symbols.SymbError e) when not test ->
    error ~test state (fun fmt -> Symbols.pp_symb_error pp_loc_error fmt e)

  | exception (TacticsArgs.TacArgError e) when not test ->
    error ~test state (fun fmt -> TacticsArgs.pp_tac_arg_error pp_loc_error fmt e)

  | exception (Tactic_soft_failure (l,e)) when not test ->
    let pp_e fmt = 
      Fmt.pf fmt "%aTactic failed: %a."
        pp_loc_error_opt l
        Tactics.pp_tac_error e in
    error ~test state pp_e

  | exception (Tactic_hard_failure (l,e)) when not test ->
    let pp_e fmt = 
      Fmt.pf fmt "%aTactic ill-formed or unapplicable: %a."  
        pp_loc_error_opt l 
        Tactics.pp_tac_error e in
    
    error ~test state pp_e

and error ~test state e =
  Printer.prt `Error "%t" e;
  if !interactive 
  then (main_loop[@tailrec]) ~test ~save:false state
  else if not test then exit 1



let start_main_loop ?(test=false) () = 
  (* Initialize definitions before parsing system description.
   * TODO this is not doable anymore (with refactoring this code)
   * concerning definitions of functions, names, ... symbols;
   * it should not matter if we do not undo the initial definitions *)
  Prover.reset ();
  main_loop ~test { mode = GoalMode; table = Symbols.builtins_table; }

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


(*------------------------------------------------------------------*)
let () =
  let exception Ok in
  let test = true in
  Checks.add_suite "Tactics" [
    "Exists Intro", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/existsintro_fail.sp" with
           | Theory.(Conv (_, Undefined "a1")) -> raise Ok)
    end ;
    "Vars not eq", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/vars_not_eq.sp" with
           | Unfinished -> raise Ok)
    end ;
    "TS not leq", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/ts_leq_not_lt.sp" with
           | Unfinished -> raise Ok)
    end ;
    "SEnc Bad SSC - INTCTXT 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/intctxt_nornd.sp" with
           | Tactic_soft_failure (_,SEncNoRandom) -> raise Ok)
    end ;
    "SEnc Bad SSC - INTCTXT 2", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/intctxt_rndnotfresh.sp" with
           | Tactic_soft_failure (_,SEncRandomNotFresh) -> raise Ok)
    end ;
    "Senc Bad SSC - INTCTXT 3", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/intctxt_sharedrnd.sp" with
           | Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;
    "Senc Bad SSC - INTCTXT 4", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/intctxt_sharedrndind.sp" with
           | Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;
    "Senc Bad SSC - CCA 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/cca_sharedrnd.sp" with
           | Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;
    "Senc Bad SSC - CCA 2", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/cca_sharedrndframe.sp" with
           | Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;
    "Senc Bad SSC - CCA 3", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/cca_nornd.sp" with
           | Tactic_soft_failure (_,SEncNoRandom) -> raise Ok)
    end ;
    "Axiom Systems - 0", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/axiom2.sp" with
           | Tactic_hard_failure (_,NoAssumpSystem) -> raise Ok)
    end ;
    "Axiom Systems - 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/axiom3.sp" with
           | Symbols.SymbError (_, Symbols.Unbound_identifier "test") ->
             raise Ok)
    end ;
    "Substitution no capture", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/capture.sp" with
           | Unfinished -> raise Ok)
    end ;
    "Not Depends", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok        
        (fun () -> 
           try run ~test "tests/alcotest/depends.sp" with
           | Tactic_soft_failure (_, Tactics.NotDepends ("A1(i)","A1(i)"))
             -> raise Ok)
    end ;
    "Fresh Not Ground", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/fresh_reach_var.sp" with
           | Tactic_soft_failure
               (_, Tactics.Failure "can only be applied on ground terms") -> 
             raise Ok)
    end ;
    "Check equalities false if unsupported terms", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok       
        (fun () -> 
           try run ~test "tests/alcotest/completion_unsupported_term.sp" with
           | Unfinished -> raise Ok)
    end ;
    "Indexed abstract", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/idx_abs.sp" with
           | Tactic_soft_failure (_,Tactics.GoalNotClosed) -> raise Ok)
    end ;
    "Indexed collision", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok        
        (fun () -> 
           try run ~test "tests/alcotest/idx_collision.sp" with
           | Unfinished -> raise Ok)
    end ;
    "Find equality", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/try.sp" with
           | Tactic_soft_failure (_,CongrFail) -> raise Ok)
    end ;
    "Undo does not maintain old truth", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/undo.sp" with
           | Unfinished -> raise Ok)
    end ;
  ] ;
  Checks.add_suite "Equivalence" [
    "Fresh Frame", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok     
        (fun () -> 
           try run ~test "tests/alcotest/fresh_frame.sp" with
           | Unfinished -> raise Ok)
    end ;
    "Fresh System", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/fresh_system.sp" with
           | Tactics.Tactic_soft_failure (_,Tactics.GoalNotClosed) -> 
             raise Ok)
    end ;
    "DDH", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/ddh.sp" with
           | Tactic_soft_failure (_,Tactics.NotDDHContext) -> raise Ok)
    end ;

    "FA Dup Input", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/fadup_input.sp" with
           | Tactic_soft_failure (_,Tactics.NoReflMacros) -> raise Ok)
    end ;
    "XOR", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/xor.sp" with
           | Unfinished -> raise Ok)
    end ;
    "XOR2", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/xor2.sp" with
           | Tactic_soft_failure (_, Failure "name is not XORed on both sides") -> 
             raise Ok)
    end ;
    "Not XOR", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/notxor.sp" with
           | Tactic_soft_failure
               (_, Failure "Can only apply xor tactic on terms of the form u XOR v")  ->
             raise Ok)
    end ;
    "Pred Init", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/pred.sp" with
           | Unfinished -> raise Ok)
    end ;
    "Pred not injective", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try run ~test "tests/alcotest/pred2.sp" with
           | Unfinished -> raise Ok)
    end ;
  ]
