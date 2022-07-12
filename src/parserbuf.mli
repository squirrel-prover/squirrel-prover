(** Module instantiating parsing from buffers. *)

(*------------------------------------------------------------------*)
(** Generic exception for user errors, that should be reported
  * with the given explanation. *)
exception Error of string

(*------------------------------------------------------------------*)
val parse_from_buf : 
  ?test:bool ->
  ?interactive:bool ->
  ((Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a) ->
  Lexing.lexbuf -> filename:string -> 
  'a
