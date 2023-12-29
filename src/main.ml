open Squirrelprover
open Squirrelhtml

open Squirrelcore
module L = Location

(* ---------------------------------------------------------------- *)

(** State of the main loop,
    with support for both history and includes. *)

module HistoryTP = History.Make(Prover)

type driver_state = {
  prover_state : Prover.state;

  (** History of prover_states. *)
  history_state : HistoryTP.history_state;

  (** Check mode for includes. *)
  check_mode : [`Check | `NoCheck];

  (** Load paths set once for all in start_main_loop. *)
  load_paths : Driver.load_paths;

  (* Current file, changed for includes. *)
  file : Driver.file;

  (** File stack can be changed with includes. *)
  file_stack : Driver.file list;
}

(** Get the next input from the current file. *)
let next_input_or_undo ~test (state : driver_state) : ProverLib.input_or_undo =
  Driver.FromFile.next_input_or_undo
    ~test ~interactive:!Driver.interactive state.file
    (Prover.get_mode state.prover_state)

(** Undo [nb_undo] previous commands. *)
let do_undo (state : driver_state) (nb_undo : int) : driver_state =
  let history_state, prover_state =
    HistoryTP.reset_state state.history_state nb_undo in
  begin match Prover.get_mode prover_state with
    | ProofMode ->
      Printer.prt `Goal "%a" (Prover.pp_goal prover_state) ()
    | GoalMode ->
      Printer.pr "%a" Action.pp_actions (Prover.get_table prover_state)
    | WaitQed -> ()
    | AllDone -> assert false
  end;
  { state with prover_state; history_state }

(** One step of main loop: execute one command. *)
let do_command
    ~main_mode
    ~(test : bool)
    (state : driver_state)
    (command : ProverLib.input_or_undo) : driver_state
  =
  match command with
  | Undo nb_undo -> do_undo state nb_undo
  | Input input ->
    let st = state.prover_state in
    let check = state.check_mode in
    let prover_state =
       Prover.do_command ~main_mode
         ~file_stack:[state.file] ~check ~test st state.file input in
    { state with prover_state }

(** The main loop of the prover. The mode defines in what state the prover is,
    e.g is it waiting for a proof script, or a system description, etc.
    [save] allows to specify if the current state must be saved, so that
    one can backtrack. *)
let rec main_loop ~main_mode ~test ?(save=true) (state : driver_state) : unit =
  if !Driver.interactive then Printer.prt `Prompt "";

  (* Save the state if instructed to do so.
   * In practice we save except after errors and the first call. *)
  let state =
    if save then
      { state with
        history_state =
          HistoryTP.save_state state.history_state state.prover_state }
    else state
  in

  match
    let cmd = next_input_or_undo ~test state in
    let new_state = do_command ~main_mode ~test state cmd in

    if !Driver.html then
      Server.update new_state.prover_state;

    new_state, Prover.get_mode new_state.prover_state
  with
  (* exit prover *)
  | _, AllDone -> Printer.pr "Goodbye!@." ;
    if !Driver.stat_filename <> "" then
      ProverTactics.pp_list_count !Driver.stat_filename;
    Driver.close_chan state.file.f_chan;
    if not test && not !Driver.html then exit 0;

  (* loop *)
  | new_state, _ ->
    if !Driver.html then Html.pp ();
    (main_loop[@tailrec]) ~main_mode ~test new_state

  (* error handling *)
  | exception e
    when Errors.is_toplevel_error ~interactive:!Driver.interactive ~test e ->
    Printer.prt `Error "%a"
      (Errors.pp_toplevel_error
         ~interactive:!Driver.interactive ~test state.file) e;
    main_loop_error ~main_mode ~test state

and main_loop_error ~main_mode ~test (state : driver_state) : unit =
  if !Driver.interactive
  then begin (* at top-level, query again *)
    assert (state.file.f_path = `Stdin);
    (main_loop[@tailrec]) ~main_mode ~test ~save:false state
  end
  else if !Driver.html then
    Fmt.epr "Error in file %s.sp:\nOutput stopped at previous call.\n"
      state.file.f_name
  else begin
    Driver.close_chan state.file.f_chan;
    if not test then exit 1
  end

let start_main_loop
    ?(test=false) ~(main_mode : [`Stdin | `File of string]) () : unit
  =
  (* Interactive is only set here. *)
  Driver.interactive := main_mode = `Stdin;
  let file = match main_mode with
    | `Stdin -> Driver.file_from_stdin ()
    | `File fname -> begin
      match
        Driver.file_from_path LP_none (Filename.remove_extension fname)
      with
      | Some f -> f
      | None ->
        Printer.prt `Error "%a ; start reading stdin…"
          Command.pp_cmd_error (FileNotFound fname);
        Driver.file_from_stdin ()
    end

  in
  let state =
    {
      prover_state = Prover.init ();
      history_state = HistoryTP.init_history_state;
      load_paths = Driver.mk_load_paths ~main_mode ();
      check_mode = `Check;
      file;
      file_stack = []
    }
  in
  (* Add interactive option to the prover state. *)
  let prover_state =
    Prover.do_set_option
      state.prover_state
      (TConfig.s_interactive, Config.Param_bool !Driver.interactive)
  in
  let state = { state with prover_state } in
  main_loop ~main_mode ~test state

let generate_html (filename : string) (html_filename : string) =
  Printer.init Printer.Html;
  if Filename.extension filename <> ".sp" then
    Command.cmd_error (InvalidExtension filename);
  Html.init filename html_filename;
  let name = Filename.chop_extension filename in
  Driver.html := true;
  start_main_loop ~test:false ~main_mode:(`File name) ();
  Html.close html_filename

let interactive_prover () =
  Printer.prt `Start "Squirrel Prover interactive mode.";
  Printer.prt `Start "Git commit: %s" Commit.hash_commit;
  Printer.init Printer.Interactive;
  Server.start ();
  Driver.html := false;
  try start_main_loop ~main_mode:`Stdin ()
  with End_of_file -> Printer.prt `Error "End of file, exiting."

let run ?(test=false) (filename : string) : unit =
  if test then begin
    Printer.init Printer.Test;
    Format.eprintf "Running %S...@." filename
  end
  else
    Printer.init Printer.File;

  if Filename.extension filename <> ".sp" then
    Command.cmd_error (InvalidExtension filename);

  if !Driver.stat_filename <> "" &&
     Filename.extension !Driver.stat_filename <> ".json"
  then
    Command.cmd_error (InvalidExtension !Driver.stat_filename);

  let name = Filename.chop_extension filename in

  Driver.html := false;
  start_main_loop ~test ~main_mode:(`File name) ()

(* Parse command line and run accordingly. *)
let main () =
  let usage =
    Fmt.str "Usage: %s [OPTION]... [FILENAME]" (Filename.basename Sys.argv.(0))
  in
  let args = ref [] in
  let html_filename = ref "" in
  let speclist = [
    ("-i",
     Arg.Set Driver.interactive,
     "Interactive mode (e.g, for proof general)");
    ("--html",
     Arg.Set_string html_filename,
     "<HTML_FILE> Output in HTML file (incompatible with -i)");
    ("-v", Arg.Set Driver.verbose, "Display more information");
    ("--stat",
     Arg.Set_string Driver.stat_filename,
     "<JSON_FILE> Output tactic usage counts in JSON file");
  ] in
  let error str =
    Arg.usage speclist usage;
    Format.eprintf "Command-line error: %s@." str
  in
  let collect arg = args := !args @ [arg] in
  let _ = Arg.parse speclist collect usage in
  Driver.html := !html_filename <> "";
  if !Driver.interactive && !Driver.html then
    error "Cannot use both --html and -i."
  else if List.length !args = 0 && not !Driver.interactive then
    error "Filename needed when not in interactive mode."
  else if List.length !args > 0 && !Driver.interactive then
    error "No file argument accepted when running in interactive mode."
  else if List.length !args > 1 then
    error "Cannot specify more than one filename."
  else if !Driver.interactive then
    interactive_prover ()
  else if !Driver.html then
    let filename = List.hd !args in
    generate_html filename !html_filename
  else
    let filename = List.hd !args in
    run filename
