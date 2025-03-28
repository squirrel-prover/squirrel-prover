(** Some functions on patterns. 
    See `Term.ml` for more functions. *)

(*------------------------------------------------------------------*)
val open_pat :
  'a Equiv.f_kind ->
  Infer.env ->
  'a Term.pat ->
  Subst.t * 'a Term.pat_op

val open_bnd_pat :
  'a Equiv.f_kind ->
  Infer.env ->
  ('a * Concrete.bound) Term.pat ->
  Subst.t * ('a * Concrete.bound) Term.pat_op

(*------------------------------------------------------------------*)
(** Make a pattern out of a formula: all universally quantified variables
    are added to [pat_vars]. *)
val pat_of_form : Term.term -> Term.term Term.pat

(*------------------------------------------------------------------*)
(** Make a pattern out of a term: all term hole [_] variables
    are added to [pat_vars]. *)
val op_pat_of_term : Term.term -> Term.term Term.pat_op
