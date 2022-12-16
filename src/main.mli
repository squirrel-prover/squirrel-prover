(** Main Module, instantiate both an interactive or a file mode. *)

(** Run the prover on an input file *)
val run : ?test:bool -> string -> unit

(** Executable entry point. Parses arguments and behaves accordingly. *)
val main : unit -> unit

exception Unfinished
