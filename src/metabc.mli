(** Main Module, instantiate both an interactive or a file mode. *)

(** [parse_next parser_fun] parse the next line of the input (or a filename)
    according to the given parsing function [parser_fun]. Used in interactive
    mode, depending on what is the type of the next expected input. *)
val parse_next : (Lexing.lexbuf -> string -> 'a) -> 'a

(** The main loop of the prover. The mode defines in what state the prover is,
    e.g is it waiting for a proof script, or a systemn description, etc.
    [save] allows to specify is the current state must be saved, so that
    one can backtrack.
*)
val main_loop : ?save:bool -> Prover.prover_mode -> 'a

(** Launches the interactive_prover mode. *)
val interactive_prover : unit -> unit

(** Run the prover on an input file *)
val run : string -> 'a

(** Executable entry point. Parses arguments and behaves accordingly. *)
val main : unit -> unit
