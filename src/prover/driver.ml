open Squirrelcore
open Squirrelfront
module L = Location

(*--TOMOVE in Config ?-------- Command flags ------------------*)
let interactive = ref false
let verbose = ref false
let html = ref false
let stat_filename = ref ""

(** A loading path: directory to lookup during includes *)
type load_path =
  | LP_dir of string
  | LP_none

type load_paths = load_path list

type t_chan = Channel of in_channel | String of string

type file = {
  f_chan   : t_chan;                 (** channel *)
  f_name   : string;                     (** short name, no extention *)
  f_path   : [`Str | `Stdin | `File of string]; (** file path *)
  f_lexbuf : Sedlexing.lexbuf;
}

(** Print precise location error (to be caught by emacs) *)
let pp_loc_error (file:file) ppf loc =
  match file.f_path with
  | `Str ->
    let (_, curr_p) = Sedlexing.lexing_positions file.f_lexbuf in
    let startpos = curr_p.pos_cnum in
    Fmt.pf ppf
      "[error-%d-%d]@;"
      (max 0 (loc.Location.loc_bchar - startpos))
      (max 0 (loc.Location.loc_echar - startpos))
  | `Stdin ->
    let lexbuf = Sedlexing.Utf8.from_channel stdin in
    let (_, curr_p) = Sedlexing.lexing_positions lexbuf in
    let startpos = curr_p.pos_cnum in
    Fmt.pf ppf
      "[error-%d-%d]@;"
      (max 0 (loc.Location.loc_bchar - startpos))
      (max 0 (loc.Location.loc_echar - startpos))
  | `File f ->
    let loc = { loc with Location.loc_fname = f; } in
    Fmt.pf ppf "%s:@;" (Location.tostring loc)

let pp_loc_error_opt (file:file) ppf = function
  | None -> ()
  | Some l -> pp_loc_error file ppf l

let check_cycle (file_stack : file list) (name : string) : unit =
  let has_cycle =
    List.exists (fun file -> file.f_name = name) file_stack
  in
  if has_cycle then Command.cmd_error (IncludeCycle name)

let get_lexbuf (file : file) : string * Sedlexing.lexbuf = 
  let lexbuf = match file.f_path with
    | `Stdin -> Sedlexing.Utf8.from_channel stdin
    (* we need to re-compute the lexer buffer from the input channel, or error
       messages are not acurate afterward. I do not understand why exactly (the
       lexer buffer positions must not be properly updated somewhere). *)

    | `Str | `File _ -> file.f_lexbuf
  in
  file.f_name ^ ".sp", lexbuf

(** Get the next input from lexing buffer. *)
let next_input
      ~test ~interactive ~filename (lexbuf:Sedlexing.lexbuf)
      (p_mode:ProverLib.prover_mode)
    : ProverLib.input
=
  Parserbuf.parse_from_buf
    ~test ~interactive
    (* ↓ can also be WaitQed since the parser can read intern tactics
       and the prover will ignore them anyway in `NoCheck mode *)
    (if (p_mode = ProverLib.ProofMode) || (p_mode = ProverLib.WaitQed) then
       Parser.top_proofmode
     else
       Parser.interactive)
    lexbuf ~filename

(** Get the next input or undo from lexing buffer. *)
let next_input_or_undo
      ~test ~interactive ~filename (lexbuf:Sedlexing.lexbuf)
      (p_mode:ProverLib.prover_mode)
    : ProverLib.input_or_undo
=
  Parserbuf.parse_from_buf
    ~test ~interactive
    (* ↓ can also be WaitQed since the parser can read intern tactics
       and the prover will ignore them anyway in `NoCheck mode *)
    (if (p_mode = ProverLib.ProofMode) || (p_mode = ProverLib.WaitQed) then
       Parser.top_proofmode_or_undo
     else
       Parser.interactive_or_undo)
    lexbuf ~filename

(** Get next inputs from current file. *)
module FromFile = struct

  let next_input
        ~test ~interactive (file : file) (p_mode: ProverLib.prover_mode)
    : ProverLib.input
  =
    let filename, lexbuf = get_lexbuf file in
    next_input ~test ~interactive ~filename lexbuf p_mode

  let next_input_or_undo
        ~test ~interactive (file : file) (p_mode: ProverLib.prover_mode)
    : ProverLib.input_or_undo
  =
    let filename, lexbuf = get_lexbuf file in
    next_input_or_undo ~test ~interactive ~filename lexbuf p_mode

end

(*--------------- Driver -------------------------------------------*)
let file_from_stdin () : file =
  { f_chan = Channel stdin;
    f_name = "#stdin";
    f_path = `Stdin;
    f_lexbuf = Sedlexing.Utf8.from_channel stdin; }

let dummy_file () : file =
  { f_chan = Channel stdin;
    f_name = "#dummy";
    f_path = `Stdin;
    f_lexbuf = Sedlexing.Utf8.from_channel stdin; }

let file_from_str (s:string) : file =
  { f_chan = String s;
    f_name = "#str";
    f_path = `Str;
    f_lexbuf = Sedlexing.Utf8.from_string s; }
    
(*--------------- Driver -------------------------------------------*)
let file_from_path (dir : load_path) (partial_path : string) : file option =
  let partial_path_ext = partial_path ^ ".sp" in
  try
    let path = match dir with
      | LP_none    -> partial_path_ext
      | LP_dir dir -> Filename.concat dir partial_path_ext
    in

    let chan = Stdlib.open_in path in
    let lexbuf = Sedlexing.Utf8.from_channel chan in

    Some { f_chan   = Channel chan;
           f_name   = partial_path;
           f_path   = `File path;
           f_lexbuf = lexbuf; }
  with
  | Sys_error _ -> None

(*------ TOMOVE in Utils or Commandline ? --------------------------*)
let valid_theory_regexp = Str.regexp {|[a-zA-Z][[a-zA-Z0-9]*|}

(** try to locate a file according to some loading paths *) 
let locate ?(is_name=true) (lds : load_paths) (name : string) : file =
  (* FIXME is it relevant ↓ ? *)
  if is_name && 
     not (Str.string_partial_match valid_theory_regexp name 0) then
    Command.cmd_error (InvalidTheoryName name);

  let rec try_dirs (dirs : load_paths) : file =
    match dirs with
    | [] -> Command.cmd_error (IncludeNotFound name)
    | dir :: dirs ->
       match file_from_path dir name with
       | Some file -> file
       | None -> try_dirs dirs
  in
  try_dirs lds

let include_get_file (file_stack : file list)
    (load_paths:load_paths) (path : ProverLib.load_path) : file =
  match path with
  | Name name ->
    check_cycle file_stack (L.unloc name);
    locate load_paths (L.unloc name)
  | Path name -> 
    check_cycle file_stack (Filename.basename (L.unloc name));
    locate ~is_name:false load_paths 
      (Filename.chop_extension (L.unloc name))

let mk_load_paths ~main_mode () : load_paths =
  let exec_dir = Filename.dirname Sys.executable_name in
  let theory_dir = Filename.concat exec_dir "theories" in
  let theory_load_path = LP_dir theory_dir in
  let top_load_path =
    match main_mode with
    | `Stdin     -> LP_dir (Sys.getcwd ())
    | `File path -> LP_dir (Filename.dirname path)
  in
  [top_load_path; theory_load_path]

let close_chan : t_chan -> unit = function
  | Channel chan -> Stdlib.close_in_noerr chan
  | String _ -> ()
