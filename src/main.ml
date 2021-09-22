open Utils

module L = Location

module Initialization = struct
  (* Opening these modules is only useful for their side effects,
   * e.g. registering tactics. *)
  open LowTactics
  open TraceTactics
  open EquivTactics
  open HighTactics
end

let usage = Printer.strf "Usage: %s filename" (Filename.basename Sys.argv.(0))

(*------------------------------------------------------------------*)
(** A loading path: directory to lookup during includes *)
type load_path = 
  | LP_dir of string 
  | LP_none

type load_paths = load_path list

type file = { 
  f_name   : string;                     (** short name, no extention *)
  f_path   : [`Stdin | `File of string]; (** file path *)
  f_lexbuf : Lexing.lexbuf;
}

(** State of the main loop. *)
(* TODO: include everything currently handled statefully in Prover.ml *)
type main_state = {
  mode  : Prover.prover_mode;
  table : Symbols.table;

  interactive : bool;

  load_paths : load_paths;
  (** load paths *)

  file : file;
  (** current file *) 

  file_stack : file list;
  (** stack of nested opened files *)
}

(*------------------------------------------------------------------*)
let get_lexbuf (state : main_state) : string * Lexing.lexbuf =
  let lexbuf = match state.file.f_path with
    | `Stdin -> Lexing.from_channel stdin
    (* we need to re-compute the lexer buffer from the input channel, or error
       messages are not acurate afterward. I do not understand why exactly (the
       lexer buffer positions must not be properly updated somewhere). *)

    | `File f -> state.file.f_lexbuf 
  in
  state.file.f_name ^ ".sp", lexbuf

(*------------------------------------------------------------------*)
(** Print precise location error (to be caught by emacs) *)
let pp_loc_error state ppf loc =
  if state.interactive then
    match state.file.f_path with
    | `Stdin ->
      let lexbuf = Lexing.from_channel stdin in
      let startpos = lexbuf.Lexing.lex_curr_p.pos_cnum in
      Fmt.pf ppf
        "[error-%d-%d]"
        (max 0 (loc.L.loc_bchar - startpos))
        (max 0 (loc.L.loc_echar - startpos))
    | `File f ->
      let loc = { loc with L.loc_fname = f; } in
      Fmt.pf ppf "%s:@;" (L.tostring loc)
 

let pp_loc_error_opt state ppf = function
  | None -> ()
  | Some l -> pp_loc_error state ppf l

type cmd_error =
  | Unexpected_command
  | AbortIncompleteProof
  | InvalidExtention  of string
  | StartProofError   of string
  | InvalidTheoryName of string
  | IncludeCycle      of string
  | IncludeNotFound   of string
  | IncludeFailed     of (Format.formatter -> unit)

exception Cmd_error of cmd_error

let pp_cmd_error fmt = function
  | Unexpected_command   -> Fmt.pf fmt "Unexpected command."

  | StartProofError s    -> Fmt.pf fmt "%s" s

  | AbortIncompleteProof -> Fmt.pf fmt "Trying to abort a completed proof."

  | InvalidTheoryName s  -> Fmt.pf fmt "invalid theory name %s" s

  | IncludeCycle s       -> Fmt.pf fmt "include cycle (%s)" s

  | IncludeNotFound s    -> Fmt.pf fmt "could not locate theory: %s" s

  | InvalidExtention s   -> Fmt.pf fmt "invalid extention (not a .sp): %s" s

  | IncludeFailed err    -> Fmt.pf fmt "%t" err

let cmd_error e = raise (Cmd_error e)


(*------------------------------------------------------------------*)
let valid_theory_regexp = Pcre.regexp "[a-zA-Z][[a-zA-Z0-9]*"

let check_cycle (state : main_state) (name : string) : unit =  
  let has_cycle =
    List.exists (fun file -> file.f_name = name) state.file_stack 
  in
  if has_cycle then cmd_error (IncludeCycle name)

let file_from_stdin () : file =
  { f_name = "#stdin";
    f_path = `Stdin;
    f_lexbuf = Lexing.from_channel stdin; }

let file_from_path (dir : load_path) (name : string) : file option =
  let filename = name ^ ".sp" in

  try
    let path = match dir with
      | LP_none    -> filename
      | LP_dir dir -> Filename.concat dir filename
    in
    
    Fmt.epr "trying: %s@." path;

    let chan = Stdlib.open_in path in
    let lexbuf = Lexing.from_channel chan in

    Some { f_name   = name;
           f_path   = `File filename;
           f_lexbuf = lexbuf; }
  with
  | Sys_error _ -> None

(** try to locate a file according to some loading paths *)
let locate (lds : load_paths) (name : string) : file =
  if not (Pcre.pmatch ~rex:valid_theory_regexp name) then    
    cmd_error (InvalidTheoryName name);  (* FIXME: location *)
 
  let rec try_dirs (dirs : load_paths) : file =
    match dirs with
    | [] -> cmd_error (IncludeNotFound name)
    | dir :: dirs -> match file_from_path dir name with
      | Some file -> file
      | None -> try_dirs dirs
  in

  try_dirs lds


let include_get_file (state : main_state) (name : Theory.lsymb) : file =
  check_cycle state (L.unloc name);

  locate state.load_paths (L.unloc name)
 
(*------------------------------------------------------------------*)
(** {2 Error handling} *)

open Tactics

(** check if an exception is handled *)
let is_toplevel_error ~test (e : exn) : bool = 
  match e with
  | Parserbuf.Error         _
  | Prover.ParseError       _ 
  | Cmd_error               _
  | Process.ProcError       _ 
  | Prover.Decl_error       _ 
  | Theory.Conv             _  
  | Symbols.SymbError       _  
  | TacticsArgs.TacArgError _  
  | Tactic_soft_failure     _  
  | Tactic_hard_failure     _ -> not test 

  | _ -> false

let pp_toplevel_error 
    ~test
    (state : main_state) 
    (fmt : Format.formatter) 
    (e : exn) : unit 
  =
  let pp_loc_error     = pp_loc_error     state in
  let pp_loc_error_opt = pp_loc_error_opt state in

  match e with
  | Parserbuf.Error s ->
    Fmt.string fmt s

  | Prover.ParseError s ->
    Fmt.string fmt s

  | Cmd_error e ->
    pp_cmd_error fmt e

  | Process.ProcError e ->
    (Process.pp_proc_error pp_loc_error) fmt e

  | Prover.Decl_error e when not test ->
    (Prover.pp_decl_error pp_loc_error) fmt e

  | Theory.Conv e when not test ->
    (Theory.pp_error pp_loc_error) fmt e

  | Symbols.SymbError e when not test ->
    (Symbols.pp_symb_error pp_loc_error) fmt e

  | TacticsArgs.TacArgError e when not test ->
    (TacticsArgs.pp_tac_arg_error pp_loc_error) fmt e

  | Tactic_soft_failure (l,e) when not test ->
    Fmt.pf fmt "%aTactic failed: %a"
      pp_loc_error_opt l
      Tactics.pp_tac_error_i e

  | Tactic_hard_failure (l,e) when not test ->
    Fmt.pf fmt "%aTactic ill-formed or unapplicable: %a"
      pp_loc_error_opt l
      Tactics.pp_tac_error_i e
      
  | _ -> assert false

(*------------------------------------------------------------------*)

exception Unfinished

(** Get the next input from the current file. *)
let next_input ~test (state : main_state) : Prover.parsed_input =
  let filename, lexbuf = get_lexbuf state in
  Parserbuf.parse_from_buf
    ~test ~interactive:state.interactive
    Parser.interactive lexbuf ~filename

(** The main loop body: do one command *)
let rec do_command
    ~(test : bool) 
    (state : main_state) 
    (command : Prover.parsed_input) : main_state 
  =
  match state.mode, command with
    | mode, ParsedUndo nb_undo ->
      let new_mode, new_table = Prover.reset_state nb_undo in
      let () = match new_mode with
        | ProofMode -> Printer.pr "%a" Prover.pp_goal ()
        | GoalMode -> Printer.pr "%a" Action.pp_actions new_table
        | WaitQed -> ()
        | AllDone -> assert false in
      { state with mode = new_mode; table = new_table; }

    | GoalMode, ParsedInputDescr decls ->
      let hint_db = Prover.current_hint_db () in
      let table = Prover.declare_list state.table hint_db decls in
      { state with mode = GoalMode; table = table; }

    | ProofMode, ParsedTactic utac ->
      if not state.interactive then
        Printer.prt `Prompt "%a" Prover.pp_ast utac ;

      begin match Prover.eval_tactic utac with
      | true ->
          Printer.prt `Goal "Goal %s is proved"
            (match Prover.current_goal_name () with
               | Some i -> i
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

    | GoalMode, ParsedHint h ->
      let db = Prover.current_hint_db () in
      let db =
        match h with
        | Hint.Hint_rewrite id -> Prover.add_hint_rewrite id db
      in
      Prover.set_hint_db db;
      state

    | GoalMode, ParsedSetOption sp ->
      Config.set_param sp;
      state

    | GoalMode, ParsedGoal g ->
      let hint_db = Prover.current_hint_db () in
      let i,f =
        Prover.declare_new_goal state.table hint_db g
      in
      Printer.pr "@[<v 2>Goal %s :@;@[%a@]@]@."
        i
        Goal.pp_init f;
      state

    | GoalMode, ParsedProof ->
      begin match Prover.start_proof () with
        | None ->
            Printer.pr "%a" Prover.pp_goal ();
            { state with mode = ProofMode }
        | Some es -> cmd_error (StartProofError es)
      end

    | GoalMode, ParsedInclude fn -> 
      (* save prover state, in case the include fails *)
      let prover_state = Prover.get_state state.mode state.table in

      let file = include_get_file state fn in
      let file_stack = state.file :: state.file_stack in

      Prover.push_pt_history ();

      let incl_state = { state with file; file_stack; } in

      (* try to do the include *)
      begin try
          let final_state = do_all_commands ~test incl_state in
          Printer.prt `Warning "loaded: %s.sp@;" final_state.file.f_name;

          Prover.pop_pt_history (); 

          { final_state with file = state.file; file_stack = state.file_stack; }

        (* include failed, revert state *)
        with e when is_toplevel_error ~test e -> 
          let err_mess fmt =
            Fmt.pf fmt "@[<v 0>include %s failed:@;@[%a@]@]" 
              (L.unloc fn)
            (pp_toplevel_error ~test incl_state) e
          in
          
          let _ : Prover.prover_mode * Symbols.table =
            Prover.reset_from_state prover_state 
          in
          cmd_error (IncludeFailed err_mess)
      end

    | GoalMode, EOF ->
      assert (state.file_stack = []);
      { state with mode = AllDone; }

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

(** Do all command from a file until EOF is reached *)
and do_all_commands ~(test : bool) (state : main_state) : main_state =
  match next_input ~test state with
  | EOF -> state
  | cmd -> do_all_commands ~test (do_command ~test state cmd)


(** The main loop of the prover. The mode defines in what state the prover is,
    e.g is it waiting for a proof script, or a system description, etc.
    [save] allows to specify is the current state must be saved, so that
    one can backtrack.
*)
let rec main_loop ~test ?(save=true) (state : main_state) =
  if state.interactive then Printer.prt `Prompt "";

  (* Save the state if instructed to do so.
   * In practice we save except after errors and the first call. *)
  if save then Prover.save_state state.mode state.table ;

  match
    let cmd = next_input ~test state in
    let new_state = do_command ~test state cmd in
    new_state, new_state.mode 
  with
  (* exit prover *)
  | _, AllDone -> Printer.pr "Goodbye!@." ; if not test then exit 0

  (* loop *)
  | new_state, _ -> (main_loop[@tailrec]) ~test new_state

  (* error handling *)
  | exception e when is_toplevel_error ~test e -> 
    Printer.prt `Error "%a" (pp_toplevel_error ~test state) e;
    main_loop_error ~test state

and main_loop_error ~test (state : main_state) : unit =
  if state.interactive
  then begin (* at top-level, query again *)
    assert (state.file.f_path = `Stdin);    
    (main_loop[@tailrec]) ~test ~save:false state
  end
  else if not test then exit 1


let mk_load_paths ~main_mode () : load_paths =
  let exec_dir = Filename.dirname Sys.executable_name in
  (* let exec_dir = Filename.dirname (Sys.argv.(0)) in *)
  let theory_dir = 
    Filename.(concat exec_dir "theories")
  in
  let theory_load_path = LP_dir theory_dir in
  let top_load_path =
    match main_mode with
    | `Stdin     -> LP_dir (Sys.getcwd ())
    | `File path -> LP_dir (Filename.dirname path)
  in
  [top_load_path; theory_load_path] 

let start_main_loop
    ?(test=false) 
    ~(main_mode : [`Stdin | `File of string]) 
    () : unit
  =
  let interactive = main_mode = `Stdin in  
  let file = match main_mode with
    | `Stdin -> file_from_stdin ()
    | `File fname -> locate [LP_none] fname
  in

  Prover.reset ();
  let state = {
    mode = GoalMode; 
    table = Symbols.builtins_table; 
    interactive;

    load_paths = mk_load_paths ~main_mode ();

    file;

    file_stack = []; } 
  in

  main_loop ~test state

let interactive_prover () : unit =
  Printer.prt `Start "Squirrel Prover interactive mode.";
  Printer.prt `Start "Git commit: %s" Commit.hash_commit;
  Printer.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
  try start_main_loop ~main_mode:`Stdin ()
  with End_of_file -> Printer.prt `Error "End of file, exiting."

let run ?(test=false) (filename : string) : unit =
  if test then begin
    Printer.printer_mode := Printer.Test;
    Format.eprintf "Running %S...@." filename
  end;
  Printer.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);

  if Filename.extension filename <> ".sp" then
    cmd_error (InvalidExtention filename);

  let name = Filename.chop_extension filename in

  start_main_loop ~test ~main_mode:(`File name) ()


let main () =
  let args = ref [] in
  let verbose = ref false in
  let interactive = ref false in
  
  let speclist = [
    ("-i", Arg.Set interactive, "interactive mode (e.g, for proof general)");
    ("-v", Arg.Set verbose, "display more informations");
  ] in

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

  (*------------------------------------------------------------------*)
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
           | Tactic_soft_failure (_,Tactics.NoReflMacroVar) -> raise Ok)
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
           | Tactic_soft_failure
               (_, Failure "name is not XORed on both sides") ->
             raise Ok)
    end ;
    "Not XOR", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/notxor.sp" with
           | Tactic_soft_failure
               (_, Failure "Xor can only be applied on a term with at least one \
                            occurrence of a term xor(t,k)")  ->
             raise Ok)
    end ;
    "Pred Init", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/pred.sp" with
           | Unfinished -> raise Ok)
    end ;
    "ES.to_trace_sequent", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/equiv_to_trace.sp" with
           | Tactic_soft_failure
               (_, HypUnknown "H") -> raise Ok)
    end
  ];

  (*------------------------------------------------------------------*)
  Checks.add_suite "Include" [
    "Cycle", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/IncludeCycle.sp" with
           | Cmd_error (IncludeCycle _) -> raise Ok)
    end ;
    "Theory not found", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/include-unknown.sp" with
           | Cmd_error (IncludeNotFound _) -> raise Ok)
    end ;
    (* Not that in test mode, errors during an include are not wrapped 
       into a IncludeError.  *)
    "Re-define", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/include-rebind.sp" with
           | Symbols.(SymbError (_, Multiple_declarations _)) ->
             raise Ok)
    end ;
    "Re-define", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/include-rebind2.sp" with
           | Symbols.(SymbError (_, Multiple_declarations _)) ->
             raise Ok)
    end ;
  ]

