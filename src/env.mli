type t = {
  table   : Symbols.table;      (** symbol table *)
  system  : SystemExpr.t;       (** default system *)
  ty_vars : Type.tvar list;     (** free type variables *)
  vars    : Vars.env;           (** free term variables *)
}

val init : 
  table:Symbols.table ->
  ?system:SystemExpr.t ->
  ?vars:Vars.env ->
  ?ty_vars:Type.tvars ->
  unit -> t

val update :
  ?system:SystemExpr.t ->
  ?table:Symbols.table ->
  ?ty_vars:Type.tvars ->
  ?vars:Vars.env ->
  t -> 
  t

val set_table   : t -> Symbols.table  -> t 
val set_system  : t -> SystemExpr.t   -> t 
val set_ty_vars : t -> Type.tvar list -> t 
val set_vars    : t -> Vars.env       -> t 
