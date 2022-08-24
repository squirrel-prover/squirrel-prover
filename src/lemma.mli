type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
val add_lemma :
  ?loc:Location.t ->
  [ `Axiom | `Lemma ] -> Goal.statement -> Symbols.table ->
  Symbols.table

val print_all : Format.formatter -> Symbols.table -> unit

(*------------------------------------------------------------------*)
(** Get proved or assumed statement. *)
val find       : lsymb -> Symbols.table -> Goal.statement
val find_reach : lsymb -> Symbols.table -> Goal.reach_statement
val find_equiv : lsymb -> Symbols.table -> Goal.equiv_statement

val mem       : lsymb -> Symbols.table -> bool
val mem_reach : lsymb -> Symbols.table -> bool
val mem_equiv : lsymb -> Symbols.table -> bool

(*------------------------------------------------------------------*)
val find_kind : lsymb -> Symbols.table -> [`Axiom | `Lemma] 

val pp_kind : Format.formatter -> [`Axiom | `Lemma] -> unit
