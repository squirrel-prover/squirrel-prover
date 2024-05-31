(** Tactic argument conversion.
    Includes [TacticsArgs] *)

include module type of TacticsArgs

(*------------------------------------------------------------------*)
val as_p_path : parser_arg list -> Symbols.p_path option

val convert_args : Env.t -> parser_arg list -> esort -> Equiv.any_form -> earg
