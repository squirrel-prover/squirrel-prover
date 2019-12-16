(** {2 Macro expansions} *)

(** Tells whether a macro symbol can be expanded when applied
  * at a particular timestamp. *)
val is_defined : Term.Macro.ns Symbols.t -> Term.timestamp -> bool

(** Return the term corresponding to the declared macro,
  * if the macro can be expanded. *)
val get_definition :
  Term.Macro.ns Symbols.t -> Action.index list -> Term.timestamp -> Term.term

(** When [m] is a global macro symbol,
  * [get_definition m li] return a term which resembles the one that
  * would be obtained with [get_definition m li ts] for some [ts],
  * except that it will feature meaningless action names in some places. *)
val get_dummy_definition :
  Term.Macro.ns Symbols.t -> Action.index list -> Term.term
