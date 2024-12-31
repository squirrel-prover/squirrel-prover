(** Tactic argument conversion.
    Includes [TacticsArgs] *)

include module type of TacticsArgs

(*------------------------------------------------------------------*)
val as_p_path : parser_arg list -> Symbols.p_path option

(** Find all occurrences of [pat] in [target], where [pat] is a term
    with holes [_].
    [ienv] is an optional inference env. for free variables in [pat]. *)
val occurrences_of_pat :
  ?ienv:Infer.env -> Env.t ->
  Term.t -> target:Equiv.any_form ->
  Term.t list

val convert_args : Env.t -> parser_arg list -> esort -> Equiv.any_form -> earg
