(** Completion of equalities and disequalities set *)
open Term
open Bformula

type state

(** [complete l] construct a complete term rewritting system from the set of
    equations inside l *)
val complete : (term * term) list -> state

(** [check_disequalities s l] checks that all disequalities inside [l] hold
    w.r.t [s] *)
val check_disequalities : state -> (term * term) list -> bool

(** [check_equalities s l] checks that all equalities inside [l] hold
    w.r.t [s] *)
val check_equalities : state -> (term * term) list -> bool

(** [name_index_cnstrs state l] looks for all names that are equal w.r.t. the
    rewrite relation in [state], and add the corresponding index equalities.
    E.g., if [n[i,j]] and [n[k,l]] are equal, then the returned list
    would contain [i=k] and [j=l]. *)
val name_index_cnstrs : state -> term list -> trace_formula_atom bformula list


(** [name_indep_cnstrs state l] looks for all name equals to a term w.r.t. the
    rewrite relation in [state], and adds the fact that the name must be equal
    to one of the name appearing inside the term. *)
val name_indep_cnstrs : state -> term list -> Formula.formula list

(** [constant_index_cnstrs] is the same as [name_index_cnstrs], but for
    constant function symbols equalities. *)
val constant_index_cnstrs :
  fname -> state -> term list -> trace_formula_atom bformula list
