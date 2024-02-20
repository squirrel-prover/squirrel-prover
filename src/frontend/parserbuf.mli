(** Module instantiating parsing from Sedlexing buffers.

    This module should perhaps disappear, as it is only used by {!Driver}
    except for testing parsing directly without going through the execution
    of prover commands. *)

(** Generic exception for user errors, that should be reported
    with the given explanation. *)
exception Error of string

(** [parse_from_buf ~test ~interactive ~filename parser lexbuf]
    runs a parser on the lexbuf, and reports errors according
    to all the other arguments. *)
val parse_from_buf :
  ?test:bool ->
  ?interactive:bool ->
  ((Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a) ->
  Sedlexing.lexbuf -> filename:string ->
  'a
