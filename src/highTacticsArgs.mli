(** Tactic argument conversion.
    Includes [TacticsArgs] *)

include module type of TacticsArgs

(*------------------------------------------------------------------*)
val convert_as_lsymb : parser_arg list -> lsymb option

val convert_args : Env.t -> parser_arg list -> esort -> Equiv.any_form -> earg
