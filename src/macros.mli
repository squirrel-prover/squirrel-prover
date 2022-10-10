(** Declaring and unfolding macros *)

module SE = SystemExpr

(*------------------------------------------------------------------*)
(** {2 Global macro definitions} *)

(** Declare a global macro (whose meaning is the same accross
    several actions, which is useful to model let-expressions)
    given a term abstracted over input variables, indices,
    and some timestamp.
    A fresh name is generated for the macro if needed. *)
val declare_global :
  Symbols.table ->
  System.t ->
  Symbols.lsymb ->
  suffix:[`Large | `Strict] ->
  action:Action.shape ->
  inputs:Vars.var list ->
  indices:Vars.var list ->
  ts:Vars.var ->
  Term.term ->
  Type.ty ->
  Symbols.table * Symbols.macro 

(*------------------------------------------------------------------*)
(** {2 Macro expansions} *)

type def_result = [ `Def of Term.term | `Undef | `MaybeDef ]

(** A expand context:
    - [InSequent]: when in a sequent. Most common mode.
    - [InGlobal {inputs}]: when in a global macro definition.
      In that case, [inputs] are the inputs variables of the global 
      macro we are doing the expansion in. *)
type expand_context = InSequent | InGlobal of { inputs : Vars.vars }

(*------------------------------------------------------------------*)
(** [get_definition context macro ~args ts] returns the expansion of 
    [macro(args)] at [ts],
    if the macro can be expanded.
    Does *not* check that the timestamp happens!
    The [context] is only used to determine whether [ts] is equal
    to some action in the trace model.

    Returns [`Def body] when the macro expands to [body],
    [`Undef] if the macro has no meaning at [ts],
    and [`MaybeDef] if the status is unknown (typically
    because [t] is unknown). *)
val get_definition :
  ?mode:expand_context ->
  Constr.trace_cntxt ->
  Term.msymb -> args:Term.term list -> ts:Term.term ->
  def_result

(** Same as [get_definition] but raises a soft failure if the macro
    cannot be expanded. *)
val get_definition_exn :
  ?mode:expand_context ->
  Constr.trace_cntxt ->
  Term.msymb -> args:Term.term list -> ts:Term.term ->
  Term.term

(** Variant of [get_definition] without dependency on [Constr] module,
    where the timestamp is directly passed as an action.
    Unlike [get_definition] it only returns [`Def body] or [`Undef]
    since we can always determine whether a macro is defined or not at
    a given action. *)
val get_definition_nocntxt :
  SE.fset -> Symbols.table ->
  Term.msymb -> args:Term.term list ->
  Symbols.action -> Term.term list ->
  [ `Def of Term.term | `Undef ]

(** When [m] is a global macro symbol,
    [get_definition se table m li] return a term which resembles the one that
    would be obtained with [get_definition m li ts] for some [ts],
    except that it will feature meaningless action names in some places. *)
val get_dummy_definition :
  Symbols.table -> SE.fset -> Term.msymb -> args:Term.term list -> Term.term

(*------------------------------------------------------------------*)
type system_map_arg =
  | ADescr  of Action.descr 
  | AGlobal of { is : Vars.vars; ts : Vars.var;
                 ac_descrs : Action.descr list; inputs : Vars.vars }
(* ac_descrs is the list of actions that have a shape where the macro
   is defined *)

(*------------------------------------------------------------------*)
(** Given the name [ns] of a macro as well as a function [f] over
    terms, an [old_single_system] and a [new_single_system], takes the
    existing definition of [ns] in the old system, applies [f] to the
    existing definition, and update the value of [ns] accordingly in
    the new system. *)
val update_global_data :
  Symbols.table -> 
  Symbols.macro -> 
  Symbols.macro_def -> 
  System.Single.t ->
  System.Single.t ->
  (system_map_arg -> Symbols.macro -> Term.term -> Term.term) -> 
  Symbols.table
    
(*------------------------------------------------------------------*)
(** {2 Utilities} *)

(** Type of the output a macro. *)
val ty_out : Symbols.table -> Symbols.macro -> Type.ty 

(** Types of the arguments of a macro. *)
val ty_args : Symbols.table -> Symbols.macro -> Type.ty list 

val is_global : Symbols.table -> Symbols.macro -> bool

