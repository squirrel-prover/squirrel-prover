(*------------------------------------------------------------------*)
type t = {
  table   : Symbols.table;      (** symbol table *)
  system  : SystemExpr.context; (** default systems *)
  ty_vars : Type.tvar list;     (** free type variables *)
  vars    : Vars.env;           (** free term variables *)
}

(** Historically the system was a system expression, but it has changed
    to a context. For simplicity the field is still named system for now. *)

(*------------------------------------------------------------------*)
val init :
  table:Symbols.table ->
  ?system:SystemExpr.context ->
  ?vars:Vars.env ->
  ?ty_vars:Type.tvars ->
  unit -> t

val update :
  ?system:SystemExpr.context ->
  ?table:Symbols.table ->
  ?ty_vars:Type.tvars ->
  ?vars:Vars.env ->
  t ->
  t

(*------------------------------------------------------------------*)
(** Straightforward setters, without any hidden modification. *)

val set_table   : t -> Symbols.table  -> t
val set_system  : t -> SystemExpr.context -> t
val set_ty_vars : t -> Type.tvar list -> t
val set_vars    : t -> Vars.env       -> t

(*------------------------------------------------------------------*)
val projs_set : Term.projs -> t -> t
