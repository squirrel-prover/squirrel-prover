open Squirrelcore
open Squirrelfront
module L = Location

type load_paths = string list

let theory_dir =
  let exec_dir = Filename.dirname Sys.executable_name in
  Filename.concat exec_dir "theories"

let mk_load_paths top_dir = [top_dir;theory_dir]

(** Drivers *)

type channel = Channel of in_channel | String of string

type t = {
  channel: channel;
  name   : string;    (** short name, no extension *)
  path   : [`Str | `Stdin | `File of string]; (** file path *)
  lexbuf : Sedlexing.lexbuf;
}

let close : t -> unit = function
  | { channel = Channel chan } -> Stdlib.close_in chan
  | _ -> ()

let dirname driver = match driver.path with
  | `File name -> Filename.dirname name
  | `Str | `Stdin -> Sys.getcwd ()

let path driver = match driver.path with
  | `File name -> Some name
  | `Str | `Stdin -> None

let name driver = driver.name

(** Errors *)

(** Print precise location error, to be caught by Emacs. *)
let pp_loc_error driver ppf loc =
  match driver.path with
  | `Str ->
    let (_, curr_p) = Sedlexing.lexing_positions driver.lexbuf in
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

let pp_loc_error_opt driver ppf = function
  | None -> ()
  | Some l -> pp_loc_error driver ppf l

let get_lexbuf driver : Sedlexing.lexbuf =
  match driver.path with
    | `Stdin -> Sedlexing.Utf8.from_channel stdin
    (* we need to re-compute the lexer buffer from the input channel, or error
       messages are not acurate afterward. I do not understand why exactly (the
       lexer buffer positions must not be properly updated somewhere).
       TODO sort this out *)
    | `Str | `File _ -> driver.lexbuf

(** Get the next input from driver. *)
let next_input
      ~test ~interactive driver
      (p_mode:ProverLib.prover_mode)
    : ProverLib.input
=
  Parserbuf.parse_from_buf
    ~test ~interactive
    ~filename:driver.name
    (if p_mode = ProverLib.ProofMode || p_mode = ProverLib.WaitQed then
       Parser.top_proofmode
     else
       Parser.interactive)
    (get_lexbuf driver)

(** Get the next input or undo from driver. *)
let next_input_or_undo
      ~test ~interactive driver
      (p_mode:ProverLib.prover_mode)
    : ProverLib.input_or_undo
=
  Parserbuf.parse_from_buf
    ~test ~interactive
    ~filename:driver.name
    (if p_mode = ProverLib.ProofMode || p_mode = ProverLib.WaitQed then
       Parser.top_proofmode_or_undo
     else
       Parser.interactive_or_undo)
    (get_lexbuf driver)

(*--------------- Driver creation functions ------------------------*)

let from_stdin () =
  { channel = Channel stdin;
    name = "#stdin";
    path = `Stdin;
    lexbuf = Sedlexing.Utf8.from_channel stdin; }

let dummy =
  { channel = Channel stdin;
    name = "#dummy";
    path = `Stdin;
    lexbuf = Sedlexing.Utf8.from_channel stdin; }

let from_string (s:string) =
  { channel = String s;
    name = "#str";
    path = `Str;
    lexbuf = Sedlexing.Utf8.from_string s; }

let from_file (path : string) : (t,exn) Result.t =
  try
    let chan = Stdlib.open_in path in
    let lexbuf = Sedlexing.Utf8.from_channel chan in
    Ok { channel= Channel chan;
           name   = Filename.(chop_extension (basename path));
           path   = `File path;
           lexbuf = lexbuf; }
  with
  | e -> Error e

(** [locate dirs filename] finds [dir] in [dirs] such that
    [dir/filename] exists, and creates a driver from it. *)
let locate (dirs : load_paths) (filename : string) =
  match
    List.find_map
      (fun dir ->
         Result.to_option
           (from_file (Filename.concat dir filename)))
      dirs
  with
  | Some driver -> driver
  | None -> Command.cmd_error (IncludeNotFound filename)

let check_cycle (driver_stack : t list) (name : string) : unit =
  let has_cycle =
    List.exists (fun driver -> driver.name = name) driver_stack
  in
  if has_cycle then Command.cmd_error (IncludeCycle name)

let from_include driver_stack load_paths (path:ProverLib.load_path) : t =
  let filename =
    match path with
    | Name name -> L.unloc name ^ ".sp"
    | Path name -> L.unloc name
  in
  check_cycle driver_stack (Filename.(chop_extension (basename filename)));
  locate load_paths filename
