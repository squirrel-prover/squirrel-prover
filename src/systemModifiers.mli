(** System modifiers are a specific kind of cryptographic tactics.
    Given a system, they apply to its totality a sound transformation
    given a cryptographic assumption, creating a new system. An axiom
    specifying that the old and new systems are indistinguishable is
    declared. *)

module SE = SystemExpr

(*------------------------------------------------------------------*)
(** Returns the updated table, and the indistinguishability axiom 
    created by the tactic. *)  
val declare_system :
  Symbols.table ->
  Hint.hint_db ->
  Decl.system_modifier ->
  Goal.statement option * Symbols.table
