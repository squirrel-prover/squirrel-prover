open Utils

type operator

val pp_operator : Format.formatter -> operator -> unit

type Symbols.data += Operator of operator

(*------------------------------------------------------------------*)
val mk : 
  name:string ->
  ty_vars:Type.tvars -> 
  args:Vars.vars -> 
  out_ty:Type.ty -> 
  body:Term.term -> 
  operator

val ftype : operator -> Type.ftype

val is_operator : Symbols.table -> Term.fsymb -> bool

val unfold : Constr.trace_cntxt -> Term.fsymb -> Term.term list -> Term.term
