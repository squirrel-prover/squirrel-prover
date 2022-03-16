val is_prefix : [`Strict | `Large] -> Action.shape -> Action.shape -> bool

(** {2 Macro definitions} *)

(** Declare a global (timestamp-dependent) macro,
    given a term abstracted over input variables, indices,
    and some timestamp.
    A fresh name is generated for the macro if needed. *)
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
    Does *not* check that the timestamp happens!
    Internally defined using [get_definition_nocntxt] below *)
val get_definition :
  Constr.trace_cntxt -> Term.msymb -> Term.term -> def_result

val get_definition_exn :
  Constr.trace_cntxt -> Term.msymb -> Term.term -> Term.term

(** Variant of [get_definition] without dependency on Constr module.
    When the Term.term argument is not of the form "Term.Action something",
    either returns [`MaybeDef] or raises [Not_found] (the latter happens when
    symb.s_symb is among [Symbols.{Output,Cond,State}] - TODO: why?),
    whereas [get_definition] does some clever stuff to find a "Term.Action sth"
    equal to the given timestamp. *)
val get_definition_nocntxt :
  SystemExpr.t -> Symbols.table -> Term.msymb -> Symbols.action Symbols.t
  -> Vars.vars -> [ `Def of Term.term | `Undef ]

(** When [m] is a global macro symbol,
    [get_definition se table m li] return a term which resembles the one that
    would be obtained with [get_definition m li ts] for some [ts],
    except that it will feature meaningless action names in some places. *)
val get_dummy_definition :
  Symbols.table -> SystemExpr.t -> Term.msymb -> Term.term

(** Given the name [ns] of a macro as well as a function [f] over
   terms, an [old_single_system] and a [new_single_system], takes the
   existing definition of [ns] in the old system, applies [f] to the
   existing definition, and update the value of [ns] accordingly in
   the new system. *)
val update_global_data :
  Symbols.table -> 
  Symbols.macro Symbols.t -> 
  Symbols.macro_def -> 
  SystemExpr.single_system ->
  SystemExpr.single_system ->
  (Term.term -> Term.term) -> 
  Symbols.table
    
