module L = Location

(*--TOMOVE in Config ?-------- Command flags ------------------*)(* {↓{ *)
let interactive = ref false
let verbose = ref false
let html = ref false
let stat_filename = ref ""
(* }↑} *)

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

(** Print precise location error (to be caught by emacs) *)
let pp_loc_error (file:file) ppf loc =
  if !interactive then
    match file.f_path with
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


let pp_loc_error_opt (file:file) ppf = function
  | None -> ()
  | Some l -> pp_loc_error file ppf l

let check_cycle (file_stack : file list) (name : string) : unit =
  let has_cycle =
    List.exists (fun file -> file.f_name = name) file_stack
  in
  if has_cycle then Command.cmd_error (IncludeCycle name)

let get_lexbuf (file : file) : string * Lexing.lexbuf = 
  let lexbuf = match file.f_path with
    | `Stdin -> Lexing.from_channel stdin
    (* we need to re-compute the lexer buffer from the input channel, or error
       messages are not acurate afterward. I do not understand why exactly (the
       lexer buffer positions must not be properly updated somewhere). *)

    | `File _ -> file.f_lexbuf
  in
  file.f_name ^ ".sp", lexbuf

(** Get the next input from the current file. Driver *)
let next_input ~test (file : file) (p_mode: ProverLib.prover_mode) :
ProverLib.input =
  let filename, lexbuf = get_lexbuf file in
  Parserbuf.parse_from_buf
    ~test ~interactive:!interactive
    (if p_mode = ProverLib.ProofMode then
       Parser.top_proofmode
     else
       Parser.interactive)
    lexbuf ~filename

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

let include_get_file (file_stack : file list)
    (load_paths:load_paths) (name : Theory.lsymb) : file =
  check_cycle file_stack (L.unloc name);
  locate load_paths (L.unloc name)

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
