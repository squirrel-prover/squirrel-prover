(** {1 Operators (mostly for concrete operators)}

    Finishes the definition of data-type started in [Symbols] that
    could not be fully done (to avoid circular dependencies) *)

open Utils

module SE = SystemExpr

(*------------------------------------------------------------------*)
(** concrete operator body *)
type body = Term.term
  
type concrete_operator = {
  name    : Symbols.fname;
  ty_vars : Type.tvar list;
  args    : Vars.var list;
  out_ty  : Type.ty;
  body    : body;
}

type Symbols.OpData.concrete_def += Val of concrete_operator

(*------------------------------------------------------------------*)
val pp_concrete_operator : concrete_operator formatter

(*------------------------------------------------------------------*)
val concrete_ftype : concrete_operator -> Type.ftype

val get_concrete_data : Symbols.table -> Symbols.fname -> concrete_operator
  
(*------------------------------------------------------------------*)
val is_concrete_operator : Symbols.table -> Symbols.fname -> bool

(*------------------------------------------------------------------*)
(** Is an operator body system-independent. *)
val is_system_indep : Symbols.table -> Symbols.fname -> bool

(*------------------------------------------------------------------*)
val unfold : 
  Symbols.table -> SE.arbitrary -> Symbols.fname ->
  Type.ty list -> Term.term list ->
  Term.term
