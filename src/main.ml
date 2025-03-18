open Squirrelprover
open Squirrelhtml

open Squirrelcore
module L = Location

(* ---------------------------------------------------------------- *)

(** Application parameters *)

let interactive = ref false
let html = ref false
let stat_filename = ref ""

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
  driver : Driver.t;

  (** File stack can be changed with includes.
      Invariant: [List.hd file_stack = file]. *)
  file_stack : Driver.t list;
}

(** Get the next input from the current file. *)
let next_input_or_undo ~test (state : driver_state) : ProverLib.input_or_undo =
  Driver.next_input_or_undo
    ~test ~interactive:!interactive state.driver
    (Prover.get_mode state.prover_state)

(** Undo [nb_undo] previous commands. *)
let do_undo (state : driver_state) (nb_undo : int) : driver_state =
  let history_state, prover_state =
    HistoryTP.reset_state state.history_state nb_undo in
  begin match Prover.get_mode prover_state with
    | ProofMode ->
      Printer.prt `Goal "%a" Prover.pp_goal prover_state
    | GoalMode ->
      Printer.pr "%a" Action.pp_actions (Prover.get_table prover_state)
    | WaitQed -> ()
    | AllDone -> assert false
  end;
  { state with prover_state; history_state }

(** One step of main loop: execute one command. *)
let do_command
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
       Prover.do_command
         ~driver_stack:[state.driver] ~check ~test st state.driver input in
    { state with prover_state }

(** The main loop of the prover. The mode defines in what state the prover is,
    e.g is it waiting for a proof script, or a system description, etc.
    [save] allows to specify if the current state must be saved, so that
    one can backtrack. *)
let rec main_loop ~test ?(save=true) (state : driver_state) : unit =
  if !interactive then Printer.prt `Prompt "";

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
    let new_state = do_command ~test state cmd in

    if !html then
      Server.update new_state.prover_state;

    new_state, Prover.get_mode new_state.prover_state
  with
  (* exit prover *)
  | _, AllDone -> Printer.pr "Goodbye!@." ;
    if !stat_filename <> "" then
      ProverTactics.pp_list_count !stat_filename;
    Driver.close state.driver;
    if not test && not !html then exit 0;

  (* loop *)
  | new_state, _ ->
    if !html then Html.pp ();
    (main_loop[@tailrec]) ~test new_state

  (* error handling *)
  | exception e
    when Errors.is_toplevel_error ~interactive:!interactive ~test e ->
    Printer.prt `Error "%a"
      (Errors.pp_toplevel_error
         ~interactive:!interactive ~test state.driver) e;
    main_loop_error ~test state

and main_loop_error ~test (state : driver_state) : unit =
  if !interactive
  then begin (* at top-level, query again *)
    assert (Driver.path state.driver = None);
    (main_loop[@tailrec]) ~test ~save:false state
  end
  else if !html then
    Fmt.epr "Error in file %s.sp:\nOutput stopped at previous call.\n"
      (Driver.name state.driver)
  else begin
    Driver.close state.driver;
    if not test then exit 1
  end

let start_main_loop ?(test=false) driver : unit =
  let state =
    {
      prover_state = Prover.init ();
      history_state = HistoryTP.init_history_state;
      load_paths = Driver.mk_load_paths (Driver.dirname driver);
      check_mode = `Check;
      driver = driver;
      file_stack = []
    }
  in
  (* Add interactive option to the prover state. *)
  let prover_state =
    Prover.do_set_option
      state.prover_state
      (L.mk_loc L._dummy TConfig.s_interactive, TConfig.Param_bool !interactive)
  in
  let state = { state with prover_state } in
  main_loop ~test state

let generate_html (filename : string) (html_filename : string) =
  Printer.init Printer.Html;
  if Filename.extension filename <> ".sp" then
    Command.cmd_error (InvalidExtension filename);
  Html.init filename html_filename;
  html := true;
  start_main_loop ~test:false (Utils.get_result (Driver.from_file filename));
  Html.close html_filename

let interactive_prover () =
  Printer.prt `Start "Squirrel Prover interactive mode.";
  Printer.prt `Start "Git commit: %s" Commit.hash_commit;
  Printer.init Printer.Interactive;
  Server.start ();
  html := false;
  try start_main_loop (Driver.from_stdin ())
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

  if !stat_filename <> "" &&
     Filename.extension !stat_filename <> ".json"
  then
    Command.cmd_error (InvalidExtension !stat_filename);

  html := false;
  start_main_loop ~test (Utils.get_result (Driver.from_file filename))

(* Parse command line and run accordingly. *)
let main () =
  let usage =
    Fmt.str "Usage: %s [OPTION]... [FILENAME]" (Filename.basename Sys.argv.(0))
  in
  let args = ref [] in
  let html_filename = ref "" in
  let speclist = [
    ("-i",
     Arg.Set interactive,
     "Interactive mode (e.g, for proof general)");
    ("--html",
     Arg.Set_string html_filename,
     "<HTML_FILE> Output in HTML file (incompatible with -i)");
    ("--stat",
     Arg.Set_string stat_filename,
     "<JSON_FILE> Output tactic usage counts in JSON file");
  ] in
  let error str =
    Arg.usage speclist usage;
    Format.eprintf "Command-line error: %s@." str
  in
  let collect arg = args := !args @ [arg] in
  let _ = Arg.parse speclist collect usage in
  html := !html_filename <> "";
  if !interactive && !html then
    error "Cannot use both --html and -i."
  else if List.length !args = 0 && not !interactive then
    error "Filename needed when not in interactive mode."
  else if List.length !args > 0 && !interactive then
    error "No file argument accepted when running in interactive mode."
  else if List.length !args > 1 then
    error "Cannot specify more than one filename."
  else if !interactive then
    interactive_prover ()
  else if !html then
    let filename = List.hd !args in
    generate_html filename !html_filename
  else
    let filename = List.hd !args in
    run filename
