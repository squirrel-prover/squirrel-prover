module L = Location

(*--TOMOVE in Config ?-------- Command flags ------------------*)(* {↓{ *)
let interactive = ref false
let verbose = ref false
let html = ref false
let stat_filename = ref ""
(* }↑} *)

(*------------- TODO move in driver lib ? -----*)(* {↓{ *)
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

module ToplevelProver = TopLevel.Make(Prover)
module HistoryTP = History.Make(ToplevelProver)

(** State of the main loop. *)
type driver_state = {
  toplvl_state : ToplevelProver.state;
  (* toplvl_state : ToplevelProver.state = {
      prover_state : Prover.state = {
        goals        : ProverLib.pending_proof list;
        table        : Symbols.table; 
        current_goal : ProverLib.pending_proof option;
        subgoals     : Goal.t list;
        bullets      : Bullets.path;
        prover_mode  : ProverLib.prover_mode;
      }
      params       : Config.params; (* save global params… *)
      option_defs  : ProverLib.option_def list; (* save global option_def *)
    }
  *)

  (* ↓ history of toplvl_state ↑ *)
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

(*--------------- Driver -------------------------------------------*)
let get_lexbuf (state : driver_state) : string * Lexing.lexbuf = 
  let lexbuf = match state.file.f_path with
    | `Stdin -> Lexing.from_channel stdin
    (* we need to re-compute the lexer buffer from the input channel, or error
       messages are not acurate afterward. I do not understand why exactly (the
       lexer buffer positions must not be properly updated somewhere). *)

    | `File _ -> state.file.f_lexbuf
  in
  state.file.f_name ^ ".sp", lexbuf

(*---------------- Driver ------------------------------------------*)
(** Print precise location error (to be caught by emacs) *)
let pp_loc_error (state:driver_state) ppf loc =
  if !interactive then
    match state.file.f_path with
    | `Stdin ->
      let lexbuf = Lexing.from_channel stdin in
      let startpos = lexbuf.Lexing.lex_curr_p.pos_cnum in
      Fmt.pf ppf
        "[error-%d-%d]@;"
        (max 0 (loc.L.loc_bchar - startpos))
        (max 0 (loc.L.loc_echar - startpos))
    | `File f ->
      let loc = { loc with L.loc_fname = f; } in
      Fmt.pf ppf "%s:@;" (L.tostring loc)


let pp_loc_error_opt (state:driver_state) ppf = function
  | None -> ()
  | Some l -> pp_loc_error state ppf l

(*--------------- Driver -------------------------------------------*)
let check_cycle (state : driver_state) (name : string) : unit =
  let has_cycle =
    List.exists (fun file -> file.f_name = name) state.file_stack
  in
  if has_cycle then Command.cmd_error (IncludeCycle name)

(*--------------- Driver -------------------------------------------*)
let file_from_stdin () : file =
  { f_name = "#stdin";
    f_path = `Stdin;
    f_lexbuf = Lexing.from_channel stdin; }
    
(*--------------- Driver -------------------------------------------*)
let file_from_path (dir : load_path) (partial_path : string) : file option =
  let partial_path_ext = partial_path ^ ".sp" in
  try
    let path = match dir with
      | LP_none    -> partial_path_ext
      | LP_dir dir -> Filename.concat dir partial_path_ext
    in

    let chan = Stdlib.open_in path in
    let lexbuf = Lexing.from_channel chan in

    Some { f_name   = partial_path;
           f_path   = `File path;
           f_lexbuf = lexbuf; }
  with
  | Sys_error _ -> None

(*------ TOMOVE in Utils or Commandline ? --------------------------*)
let valid_theory_regexp = Pcre.regexp "[a-zA-Z][[a-zA-Z0-9]*"

(** try to locate a file according to some loading paths *) 
let locate (lds : load_paths) (name : string) : file =
  if not (Pcre.pmatch ~rex:valid_theory_regexp name) then
    Command.cmd_error (InvalidTheoryName name);  (* FIXME: location *)  

  let rec try_dirs (dirs : load_paths) : file =
    match dirs with
    | [] -> Command.cmd_error (IncludeNotFound name)
    | dir :: dirs ->
       match file_from_path dir name with
       | Some file -> file
       | None -> try_dirs dirs
  in
  try_dirs lds

(*--------------- Driver -------------------------------------------*)
let include_get_file (state : driver_state) (name : Theory.lsymb) : file =
  check_cycle state (L.unloc name);
  locate state.load_paths (L.unloc name)

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

(** Get the next input from the current file. Driver *)
let next_input ~test (state : driver_state) :
ProverLib.input =
  let filename, lexbuf = get_lexbuf state in
  Parserbuf.parse_from_buf
    ~test ~interactive:!interactive
    (if ToplevelProver.get_mode state.toplvl_state = ProverLib.ProofMode then
       Parser.top_proofmode
     else
       Parser.interactive)
    lexbuf ~filename

