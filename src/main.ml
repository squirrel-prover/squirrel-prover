open Squirrelprover
open Squirreltactics
open Squirrelhtml
open Driver

(* not necessary ↓ Only for do_include *)
open Squirrelcore
module L = Location

(* maybe just include Squirreltactics for registering ? *)
module Initialization = struct
  (* Opening these modules is only useful for their side effects,
   * e.g. registering tactics - hence the use of "open!" *)
  open! LowTactics
  open! TraceTactics
  open! EquivTactics
  open! HighTactics
end

let usage = Fmt.str "Usage: %s filename" (Filename.basename Sys.argv.(0))

module HistoryTP = History.Make(Prover)

(** State of the main loop. *)
type driver_state = {
  prover_state : Prover.state;
  (* prover_state : Prover.state = {
        goals        : ProverLib.pending_proof list;
        table        : Symbols.table; 
        current_goal : ProverLib.pending_proof option;
        subgoals     : Goal.t list;
        bullets      : Bullets.path;
        prover_mode  : ProverLib.prover_mode;
    }
  *)

  (* ↓ history of prover_state ↑ *)
  history_state : HistoryTP.history_state;

  (* The check_mode can be changed regarding to includes main.ml:426 *)
  check_mode : [`Check | `NoCheck];

  (* load_paths set once for all in start_main_loop *)
  load_paths : load_paths;
  (** load paths *)

  (* current file can be changed regarding to do_include *)
  file : file;
  (** current file *)

  (* file_stack can be changed regarding to do_include *)
  file_stack : file list;
  (** stack of nested opened files *)
}

(** Get the next input from the current file. Driver *)
let next_input ~test (state : driver_state) : ProverLib.input =
  Driver.next_input_file ~test ~interactive:!interactive state.file
    (Prover.get_mode state.prover_state)

(*---------------- Main --------------------------------------------*)
let do_undo (state : driver_state) (nb_undo : int) : driver_state =
  let history_state, prover_state =
  HistoryTP.reset_state state.history_state nb_undo in
  let () = match Prover.get_mode prover_state with
    | ProofMode -> Printer.prt `Goal "%a" (Prover.pp_goal
                     prover_state) ()
    | GoalMode -> Printer.pr "%a" Action.pp_actions
                    (Prover.get_table prover_state)
    | WaitQed -> ()
    | AllDone -> assert false in
  { state with prover_state; history_state; }

(** The main loop body: do one command *)
let do_command
    ~main_mode
    ~(test : bool)
    (state : driver_state)
    (command : ProverLib.input) : driver_state
  =
  match command with 
    (* ↓ touch prover_state and history_state ↓ *)
  | Toplvl Undo nb_undo          -> do_undo state nb_undo
  | Prover _ -> 
    let st = state.prover_state in
    let check = state.check_mode in
    let prover_state = Prover.do_command ~main_mode
        ~file_stack:[state.file] ~check ~test st state.file command in
    { state with prover_state; }

(** The main loop of the prover. The mode defines in what state the prover is,
    e.g is it waiting for a proof script, or a system description, etc.
    [save] allows to specify is the current state must be saved, so that
    one can backtrack.
*)
let rec main_loop ~main_mode ~test ?(save=true) (state : driver_state) : unit =
  if !interactive then Printer.prt `Prompt "";

  (* Save the state if instructed to do so.
   * In practice we save except after errors and the first call. *)
  let state = 
    if save then
      {state with
       history_state =
         HistoryTP.save_state state.history_state state.prover_state
      }
    else state
  in

  match
    let cmd = next_input ~test state in
    let new_state = do_command ~main_mode ~test state cmd in

    if !html then
      Server.update new_state.prover_state;

    new_state, Prover.get_mode new_state.prover_state
  with
  (* exit prover *)
  | _, AllDone -> Printer.pr "Goodbye!@." ;
    if !stat_filename <> "" then
      ProverTactics.pp_list_count !stat_filename;
    Driver.close_chan state.file.f_chan;
    if not test && not !html then exit 0;

  (* loop *)
  | new_state, _ ->
    if !html then Html.pp ();
    (main_loop[@tailrec]) ~main_mode ~test new_state

  (* error handling *)
  | exception e when Errors.is_toplevel_error ~interactive:!interactive ~test e ->
    Printer.prt `Error "%a" (Errors.pp_toplevel_error ~interactive:!interactive ~test state.file) e;
    main_loop_error ~main_mode ~test state

and main_loop_error ~main_mode ~test (state : driver_state) : unit =
  if !interactive
  then begin (* at top-level, query again *)
    assert (state.file.f_path = `Stdin);
    (main_loop[@tailrec]) ~main_mode ~test ~save:false state
  end
  else if !html then 
    Fmt.epr "Error in file %s.sp:\nOutput stopped at previous call.\n" 
      state.file.f_name
  else begin
    Driver.close_chan state.file.f_chan;
    if not test then exit 1
  end

let start_main_loop
    ?(test=false) ~(main_mode : [`Stdin | `File of string]) () : unit
  =
  (* interactive is only set here *)
  interactive := main_mode = `Stdin;
  let file = match main_mode with
    | `Stdin -> file_from_stdin ()
    | `File fname -> locate [LP_none] fname
  in
  let state = {
    prover_state = Prover.init ();

    history_state = HistoryTP.init_history_state;

    (* The check_mode can be changed regarding to includes main.ml:426 *)
    check_mode = `Check;

    (* load_paths set here once for all … *)
    load_paths = mk_load_paths ~main_mode ();

    (* current file can be changed regarding to includes main.ml:426 *)
    file;

    (* file_stack can be changed regarding to includes main.ml:426 *)
    file_stack = []; }
  in
  (* add interactive option to the table *)
  let prover_state = 
    Prover.do_set_option 
      state.prover_state (TConfig.s_interactive,Config.Param_bool !interactive) 
  in
  let state = { state with prover_state; } in

  main_loop ~main_mode ~test state

let generate_html (filename : string) (html_filename : string) =
  Printer.init Printer.Html;
  if Filename.extension filename <> ".sp" then
    Command.cmd_error (InvalidExtention filename);
  Html.init filename html_filename;
  let name = Filename.chop_extension filename in
  html := true;
  start_main_loop ~test:false ~main_mode:(`File name) ();
  Html.close html_filename

let interactive_prover () =
  Printer.prt `Start "Squirrel Prover interactive mode.";
  Printer.prt `Start "Git commit: %s" Commit.hash_commit;
  Printer.init Printer.Interactive;
  Server.start ();
  html := false;
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
    Command.cmd_error (InvalidExtention filename);

  if (!stat_filename <> "") && 
     (Filename.extension !stat_filename <> ".json") then
    Command.cmd_error (InvalidExtention !stat_filename);

  let name = Filename.chop_extension filename in

  html := false;
  start_main_loop ~test ~main_mode:(`File name) ()

(* parse command line and check values before `run`ning *)
let main () =
  let args = ref [] in
  let html_filename = ref "" in
  let stat_filename = ref "" in
  let speclist = [
    ("-i", Arg.Set interactive, "interactive mode (e.g, for proof general)");
    ("--html", Arg.Set_string html_filename, "<file.html> Output a html file; Incompatible with -i");
    ("-v", Arg.Set verbose, "display more informations");
    ("--stat", Arg.Set_string stat_filename, "<stat.json> Output a json file
    with statistics (tactic count)");
  ] in

  let collect arg = args := !args @ [arg] in
  let _ = Arg.parse speclist collect usage in
  html := !html_filename <> "";
  if !interactive && !html then
    Arg.usage speclist usage
  else if List.length !args = 0 && not !interactive then
    Arg.usage speclist usage
  else if List.length !args > 0 && !interactive then
    Printer.pr "No file arguments accepted when running in interactive mode.@."
  else if !interactive then
    interactive_prover ()
  else if !html then
    let filename = List.hd !args in
    generate_html filename !html_filename
  else
    let filename = List.hd !args in
    run filename
