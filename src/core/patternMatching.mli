(*------------------------------------------------------------------*)
(** {2 Pattern-matching utilities} *)

(** Equality discriminate: return [true] if both term are never equal.
    Exploits the properties of constructors of an inductive type
    (e.g. [List.Nil] is never equal to a [List.Cons _ _]). *)
val discriminate_eq :
  Reduction.state Lazy.t ->
  Symbols.table ->
  Term.t -> Term.t -> bool

(** In-equality discriminate, try to show that [l < r] (or [l ≤ r]
    if [large]), where the standard ordering [<] is the structural
    on inductive types, ordering constructors arguments in
    lexicographic orders. *)
val discriminate_lt :
  Reduction.state Lazy.t ->
  Symbols.table ->
  large:bool ->
  Term.t -> Term.t -> bool
