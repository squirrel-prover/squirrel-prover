open Utils

(*------------------------------------------------------------------*)
module SE = SystemExprSyntax

(*------------------------------------------------------------------*)
type t = {
  ty_vars : Type.tvars;
  se_vars : SE.tagged_vars;
}

(*------------------------------------------------------------------*)
val empty : t

val pp : t formatter

(*------------------------------------------------------------------*)
module Open : sig
  type t = {
    ty_vars : Type.univars;
    se_vars : SE.Var.t list;
  }

  val empty : t

  val pp : t formatter
end
