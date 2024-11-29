module SE = SystemExpr

(*------------------------------------------------------------------*)
(** {1 Computability predicates.} 

    This file provide functions to manipulate computability predicates:
    - deducibility [u |> v] 
    - secrecy      [u *> v]

    These predicates are defined in [WeakSecrecy.sp]. *)


(** There are two kinds of computability formulas:
    - deduction     [( |> )] 
    - non-deduction [( *> )] *)
type kind = Deduce | NotDeduce

(** The type of a computability formula. *)
type form

(** Checks whether a global formula is a computability formula. 
    Notably checks that [WeakSecrecy] is loaded. *)
val is_computability : Symbols.table -> Equiv.form -> bool

(** Constructs a computability formula. 
    [left] and [left_tys] must have the same lengths.
    The [WeakSecrecy] module must be loaded. *)
val make : 
  Symbols.table -> kind -> SE.fset -> 
  left_tys:Type.ty list -> right_ty:Type.ty -> 
  left:Term.terms -> right:Term.term -> form

(*------------------------------------------------------------------*)
(** Constructs a secrecy goal from a global formula. 
    Assumes [is_computability] holds. *)
val from_global : Symbols.table -> Equiv.form -> form 

(** Constructs the global formula for a secrecy goal. *)
val to_global : form -> Equiv.form

(*------------------------------------------------------------------*)
(** Extracts the kind of secrecy goal. *)
val kind : form -> kind

(** Returns the system of the secrecy goal *)
val system : form -> SE.t

(** Returns the left-hand side of the secrecy goal. 
    In case it is a tuple, or nested tuples, flattens it as
    a list of terms. *)
val left : form -> Term.terms

(** Returns the right-hand side of the secrecy goal. *)
val right : form -> Term.term

(** Returns a new secrecy goal where the left-hand side has been updated*)
val update_left : Term.terms -> form -> form

(** Returns a new secrecy goal where the right-hand side has been updated*)
val update_right : Term.terms -> form -> form
