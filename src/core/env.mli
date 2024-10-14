open Utils
open Ppenv

module SE = SystemExprSyntax

(*------------------------------------------------------------------*)
type t = {
  table   : Symbols.table;      (** symbol table *)
  system  : SE.context;         (** default systems *)
  se_vars : SE.tagged_vars;     (** free system variables *)
  ty_vars : Type.tvar list;     (** free type variables *)
  vars    : Vars.env;           (** free term variables *)
}

(** Historically the system was a system expression, but it has changed
    to a context. For simplicity the field is still named system for now. *)

(*------------------------------------------------------------------*)
val _pp    : t formatter_p
val pp     : t formatter
val pp_dbg : t formatter
    
(*------------------------------------------------------------------*)
val init :
  table:Symbols.table ->
  ?system:SE.context ->
  ?vars:Vars.env ->
  ?ty_vars:Type.tvars ->
  ?se_vars:SE.tagged_vars ->
  unit -> t

val update :
  ?system:SE.context ->
  ?table:Symbols.table ->
  ?ty_vars:Type.tvars ->
  ?vars:Vars.env ->
  ?se_vars:SE.tagged_vars ->
  t ->
  t

(*------------------------------------------------------------------*)
(** Straightforward setters, without any hidden modification. *)

val set_table   : t -> Symbols.table  -> t
val set_system  : t -> SE.context     -> t
val set_ty_vars : t -> Type.tvar list -> t
val set_vars    : t -> Vars.env       -> t
val set_se_vars : t -> SE.env         -> t

(*------------------------------------------------------------------*)
val projs_set : Projection.t list -> t -> t

(*------------------------------------------------------------------*)
val to_params : t -> Params.t
