open Squirrelcore
(** Module instantiating parsing from buffers. *)

let () = Printexc.record_backtrace true

module L = Location

(** Generic exception for user errors, that should be reported
  * with the given explanation. *)
exception Error of string

(** Given an exception raised during parsing,
  * and a pretty-printer for the location of the error,
  * return [Some pp] where [pp] is a pretty-printer
  * describing the error to the user.
  *
  * For bad, internal errors that should be
  * reported with a backtrace, return [None]. *)
let pp_error pp_loc pp_pref_loc e = match e with
  | Parser.Error ->
      Some (fun ppf () ->
              Fmt.pf ppf
                "%aSyntax error: @[%a@]."
                pp_pref_loc ()
                pp_loc ())
  | Failure s ->
      Some (fun ppf () ->
              Fmt.pf ppf
                "%aError: @[%a@]: @,%s."
                pp_pref_loc ()
                pp_loc ()
                s)
  | _ -> None

(** Pretty-printer for parsing locations. *)
let pp_loc interactive filename lexbuf ppf () =
  let (_, curr_p) = Sedlexing.lexing_positions lexbuf in
  let lexeme = Sedlexing.Utf8.lexeme lexbuf in
  let line = curr_p.Lexing.pos_lnum in
  let col = curr_p.Lexing.pos_cnum -
              curr_p.Lexing.pos_bol in
  if not interactive then
    Fmt.pf ppf
      "in %s @,\
       at line %d char %d @,\
       before %S"
      filename
      line
      col
      lexeme
  else
    Fmt.pf ppf
      "at line %d char %d of this input @,\
       before %S"
      line
      col
      lexeme

let pp_pref_loc interactive lexbuf ppf () =
  if interactive then
    let (start_p, end_p) = Sedlexing.lexing_positions lexbuf in
    Fmt.pf ppf
      "[error-%d-%d]@;"
      start_p.pos_cnum
      end_p.pos_cnum

let parse_from_buf
    ?(test=false)
    ?(interactive=false) 
    (parse_fun : (Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a)
    (lexbuf    : Sedlexing.lexbuf)
    ~(filename  : string) : 'a 
  =
  let lexer = Sedlexing.with_tokenizer Sedlexer.token lexbuf in
  let parse_fun = MenhirLib.Convert.Simplified.traditional2revised parse_fun in
  try parse_fun lexer with e ->
    let pp_loc = pp_loc interactive filename lexbuf in
    let pp_pref_loc = pp_pref_loc interactive lexbuf in
    match pp_error pp_loc pp_pref_loc e with
    | Some pp_error ->
      if test then raise e else
      if interactive then
        let msg = Fmt.str "%a" pp_error () in
        raise (Error msg)
      else begin
        Printer.defprt `Error "%a" pp_error () ;
        exit 1
      end
    | None ->
      if test || interactive then raise e else begin
        Printer.defprt `Error
          "@[Exception %a: @,%s.@]@.@.\
           %s@."
          pp_loc ()
          (Printexc.to_string e)
          (Printexc.get_backtrace ()) ;
        exit 1
      end
