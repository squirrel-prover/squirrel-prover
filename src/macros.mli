val is_prefix : [`Strict | `Large] -> Action.shape -> Action.shape -> bool

(** {2 Macro definitions} *)

type global_data = {
  action  : [`Strict | `Large] * Action.shape;
  (** the global macro is defined at any action which is a strict or large
      suffix of [action]  *)

  inputs  : Vars.var list;
  (** inputs of the macro, as variables, in order *)

  indices : Vars.var list;
  (** free indices of the macro, which corresponds to the prefix of
      the indices of the action defining the macro *)

  ts      : Vars.var;
  (** free timestamp variable of the macro, which can only be instantiated
      by a strict suffix of [action] *)

  default_body    : Term.term;
  (** macro body shared by all systems *)

  systems_body    : (SystemExpr.single_system * Term.term) list;
  (** Optional alternative definitions of the body for a given system.
      Used by System modifiers.
  *)

}

val get_global_data : Symbols.data -> global_data option
val get_body : SystemExpr.t -> global_data -> Term.term

(** Declare a global (timestamp-dependent) macro,
  * given a term abstracted over input variables, indices,
  * and some timestamp.
  * A fresh name is generated for the macro if needed. *)
val declare_global :
  Symbols.table ->
  Symbols.lsymb ->
  suffix:[`Large | `Strict] ->
  action:Action.shape ->
  inputs:Vars.var list ->
  indices:Vars.var list ->
  ts:Vars.var ->
  Term.term ->
  Type.ty ->
  Symbols.table * Symbols.macro Symbols.t

(** {2 Macro expansions} *)

type def_result = [ `Def of Term.term | `Undef | `MaybeDef ]

(** Return the term corresponding to the declared macro,
    if the macro can be expanded.
    Does *not* check that the timestamp happens ! *)
val get_definition :
  Constr.trace_cntxt -> Term.msymb -> Term.term -> def_result

val get_definition_exn :
  Constr.trace_cntxt -> Term.msymb -> Term.term -> Term.term

(** When [m] is a global macro symbol,
  * [get_definition se table m li] return a term which resembles the one that
  * would be obtained with [get_definition m li ts] for some [ts],
  * except that it will feature meaningless action names in some places. *)
val get_dummy_definition :
  Symbols.table -> SystemExpr.t -> Term.msymb -> Term.term

val apply_global_data :
  Symbols.table -> 
  Symbols.macro Symbols.t -> 
  Symbols.macro_def -> 
  SystemExpr.single_system ->
  SystemExpr.single_system ->
  'a -> 
  (Term.term -> Term.term) -> 
  Symbols.table
    
