(** {2 Macro definitions} *)

(** Declare a global (timestamp-dependent) macro,
  * given a term abstracted over input variables, indices,
  * and some timestamp.
  * A fresh name is generated for the macro if needed. *)
val declare_global :
  Symbols.table ->
  string ->
  inputs:Vars.message list ->
  indices:Vars.index list ->
  ts:Vars.timestamp ->
  Term.message ->
  Symbols.table * Symbols.macro Symbols.t

(** Update the definition of a global (timestamp-dependent) macro. *)
val update :
  Symbols.table ->
  Symbols.macro Symbols.t ->
  Term.message ->
  Symbols.table

(** {2 Macro expansions} *)

(** Tells whether a macro symbol can be expanded when applied
  * at a particular timestamp. *)
val is_defined : Symbols.macro Symbols.t -> Term.timestamp -> bool

(** Return the term corresponding to the declared macro,
  * if the macro can be expanded. *)
val get_definition :
  Action.system -> 'a Sorts.sort ->
  Symbols.macro Symbols.t -> Vars.index list -> Term.timestamp -> 'a Term.term

(** When [m] is a global macro symbol,
  * [get_definition m li] return a term which resembles the one that
  * would be obtained with [get_definition m li ts] for some [ts],
  * except that it will feature meaningless action names in some places. *)
val get_dummy_definition :
  Action.system -> 'a Sorts.sort ->
  Symbols.macro Symbols.t -> Vars.index list -> 'a Term.term
