(** Main Module, instantiate both an interactive or a file mode. *)

(** [parse_next parser_fun] parse the next line of the input (or a filename)
    according to the given parsing function [parser_fun]. Used in interactive
    mode, depending on what is the type of the next expected input. *)
val parse_next : (Lexing.lexbuf -> string -> 'a) -> 'a

(** The main loop of the prover. *)
val start_main_loop : ?test:bool -> unit -> unit

(** Launches the interactive_prover mode. *)
val interactive_prover : unit -> unit

(** Run the prover on an input file *)
val run : ?test:bool -> string -> unit

(** Executable entry point. Parses arguments and behaves accordingly. *)
val main : unit -> unit
