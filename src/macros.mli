(** {2 Macro definitions} *)

(** Declare a global (timestamp-dependent) macro,
  * given a term abstracted over input variables, indices,
  * and some timestamp.
  * A fresh name is generated for the macro if needed. *)
val declare_global :
  Symbols.table ->
  Symbols.lsymb ->
  suffix:[`Large | `Strict] ->
  action:Action.shape ->
  inputs:Vars.message list ->
  indices:Vars.index list ->
  ts:Vars.timestamp ->
  Term.message ->
  Type.tmessage ->
  Symbols.table * Symbols.macro Symbols.t

(** {2 Macro expansions} *)

type def_result = [ `Def of Term.message | `Undef | `MaybeDef ]
                  
(** Return the term corresponding to the declared macro,
    if the macro can be expanded.
    Does *not* check that the timestamp happens ! *)
val get_definition :
  Constr.trace_cntxt -> Term.msymb -> Term.timestamp -> def_result

val get_definition_exn :
  Constr.trace_cntxt -> Term.msymb -> Term.timestamp -> Term.message

(** When [m] is a global macro symbol,
  * [get_definition se table m li] return a term which resembles the one that
  * would be obtained with [get_definition m li ts] for some [ts],
  * except that it will feature meaningless action names in some places. *)
val get_dummy_definition :
  Symbols.table -> SystemExpr.t -> Term.msymb -> Term.message
