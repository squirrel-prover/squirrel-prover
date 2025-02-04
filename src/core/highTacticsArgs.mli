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
  concrete:bool ->
  ?ienv:Infer.env -> ?in_system:SE.t ->
  Env.t ->
  Term.t -> target:Equiv.any_form ->
  Term.t list

val convert_args :
  Env.t -> parser_arg list ->
  esort -> Equiv.any_form -> earg

(** [convert_pat env t target] convert a term and fill-in possible
    term holes by looking for occurrences of [t] in [target]. *)
val convert_with_holes :
  ?ty:Type.ty -> 
  Typing.conv_env ->
  Typing.term -> Equiv.any_form -> Term.term * Type.ty
