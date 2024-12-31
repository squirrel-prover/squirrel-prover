(** Tactic argument conversion.
    Includes [TacticsArgs] *)

include module type of TacticsArgs

(*------------------------------------------------------------------*)
val as_p_path : parser_arg list -> Symbols.p_path option

(** Find all occurrences of [pat] in [target], where [pat] is a term
    with holes [_].
    Search is restricted to subterms in system [in_system], if not [None].
    [ienv] is an optional inference env. for free variables in [pat]. *)
val occurrences_of_pat :
  ?ienv:Infer.env -> ?in_system:SE.t ->
  Env.t ->
  Term.t -> target:Equiv.any_form ->
  Term.t list

val convert_args : Env.t -> parser_arg list -> esort -> Equiv.any_form -> earg
