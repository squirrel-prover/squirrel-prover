(** System modifiers are a specific kind of cryptographic tactics.
    Given a system, they apply to its totality a sound transformation
    given a cryptographic assumption, creating a new system. An axiom
    specifying that the old and new systems are indistinguishable is
    declared. *)

(** [declare_system table sdecl] returns a tuple 
    [(name, fresh_vars, goal_maker, new_system, new_table)] containing:
    - the [name] of the indistinguishability axiom introduced by the tactic
    - the fresh variables [fresh_vars] needed to define the axiom
    - the function [goal_maker] that will allow to create the correct goal 
      for the axiom, once back in the prover loop
    - a [pair_expr] composed of the original and new systems
    - the [new_table] *)  
val declare_system :
  Symbols.table ->
  Decl.system_decl_modifier ->
  string *
  Term.term list *
  (Equiv.global_form -> Equiv.any_form) *
  SystemExpr.pair *
  Symbols.table
