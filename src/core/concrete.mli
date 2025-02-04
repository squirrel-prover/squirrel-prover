include module type of LowConcrete

(*------------------------------------------------------------------*)
val reduce_bound :
  Symbols.table -> SystemExprSyntax.context -> bound -> bound

(*------------------------------------------------------------------*)
type form_type =
 | Atom_conc of Term.term
 | Atom_asym
 | Form

val form_type_to_option : ?failure:bool -> form_type -> Term.term option

val global_extract_bound : Equiv.form -> form_type
val global_set_bound : Term.term -> Equiv.form -> Equiv.form

(*------------------------------------------------------------------*)
module BoundManagement (S : Sequent.S) : sig
  val get_bound : ?failure:bool -> S.t -> Term.term option

  (** Is the conclusion a concrete atom, or is the sequent a local
      concrete sequent. *)
  val conclusion_is_concrete       : S.t -> bool

  val conclusion_is_concrete_equiv : S.t -> bool

  (** Set the bound in the conclusion of [s].

      Targets both local sequent and global sequent with a concrete
      reachability conclusion. *)
  val set_bound : Term.term -> S.t -> S.t

  (** [add_bound b s] adds [b] to the bound in the conclusion of [s].

      Targets both local sequent and global sequent with a concrete
      reachability conclusion. *)
  val add_bound   : Term.term -> S.t -> S.t

  (** Same as [add_bound], but substracting instead of adding. *)
  val minus_bound : Term.term -> S.t -> S.t

  (** [leq_bound new_b] creates an inequality subgoal justifying a
      concrete weakening to [new_bound] (i.e. asks to prove that
      [new_b ≤ b] if [b] is the bound of [s]). *)
  val leq_bound : Term.term -> S.t -> S.t

  val list_bounds_fill :
    Term.term option list -> 'a list -> S.t -> bound list * S.t list
end
