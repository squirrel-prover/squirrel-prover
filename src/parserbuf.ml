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
  if not interactive then
    Fmt.pf ppf
      "in %s @,\
       at line %d char %d @,\
       before %S"
      filename
      lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
      (lexbuf.Lexing.lex_curr_p.Lexing.pos_cnum -
       lexbuf.Lexing.lex_curr_p.Lexing.pos_bol)
      (Lexing.lexeme lexbuf)
  else
    Fmt.pf ppf
      "at line %d char %d of this input @,\
       before %S"
      lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
      (lexbuf.Lexing.lex_curr_p.Lexing.pos_cnum -
       lexbuf.Lexing.lex_curr_p.Lexing.pos_bol)
      (Lexing.lexeme lexbuf)

let pp_pref_loc interactive lexbuf ppf () =
  if interactive then
    Fmt.pf ppf
      "[error-%d-%d]@;"
      (Lexing.lexeme_start_p lexbuf).pos_cnum
      (Lexing.lexeme_end_p lexbuf).pos_cnum


let parse_from_buf
    ?(test=false)
    ?(interactive=false) 
    (parse_fun : (Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a)
    (lexbuf    : Lexing.lexbuf)
    ~(filename  : string) : 'a 
  =
  try parse_fun Lexer.token lexbuf with e ->
    let pp_loc = pp_loc interactive filename lexbuf in
    let pp_pref_loc = pp_pref_loc interactive lexbuf in
    match pp_error pp_loc pp_pref_loc e with
    | Some pp_error ->
      if test then raise e else
      if interactive then
        let msg = Fmt.str "%a" pp_error () in
        raise (Error msg)
      else begin
        Printer.prt `Error "%a" pp_error () ;
        exit 1
      end
    | None ->
      if test || interactive then raise e else begin
        Printer.prt `Error
          "@[Exception %a: @,%s.@]@.@.\
           %s@."
          pp_loc ()
          (Printexc.to_string e)
          (Printexc.get_backtrace ()) ;
        exit 1
      end
