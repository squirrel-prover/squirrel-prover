(** Declaring and unfolding macros *)

open Utils
open Ppenv

module SE = SystemExpr
  
(*------------------------------------------------------------------*)
(** {2 Macro for mutable state} *)

type Symbols.state_macro_def += StateInit_data of Vars.var list * Term.term

(** [get_init_states] returns all the initial values of declared state symbols,
    used to register the init action. *)
val get_init_states :
  Symbols.table -> (Symbols.macro * Term.terms * Term.term) list

(*------------------------------------------------------------------*)
(** {2 General macro definitions} *)
    
(*------------------------------------------------------------------*)
(** A definition of a general structured recursive macro definition:
    [m = λτ ↦ if not (happens τ) then default
              else if τ = init then tinit
              else body τ] *)
type structed_macro_data = {
  name    : Symbols.macro;        (** a macro [m] *)
  default : Term.term;            (** [m@τ] if not [happens(τ)] *)
  tinit   : Term.term;            (** [m@init] *)
  body    : Vars.var * Term.term; (** [λτ. m@τ] when [happens(τ) ∧ τ≠init] *)
  rec_ty  : Type.ty;              (** The type of [τ] *)
  ty      : Type.ty;              (** The type of the **body** of [m] *)
}

(*------------------------------------------------------------------*)
(** A general macro definition. *)
type general_macro_data = 
  | Structured of structed_macro_data
  | ProtocolMacro of [`Output | `Cond] 
  (** ad hoc macro definitions using action descriptions *)

(*------------------------------------------------------------------*)
type Symbols.general_macro_def += Macro_data of general_macro_data

(*------------------------------------------------------------------*)
val get_general_macro_data : Symbols.general_macro_def -> general_macro_data 
val as_general_macro : Symbols.data -> general_macro_data 

(*------------------------------------------------------------------*)
(** {2 Execution models} *)

(** An execution model *)
type exec_model = Classical | PostQuantum

(** The definition of an execution model *)    
type exec_model_def = {
  np : Symbols.npath;
  (** namespace where this execution model will define its macros *)

  input_name : Symbols.macro;
  (** input macro in this execution model *)

  output_name : Symbols.macro;
  (** output macro in this execution model *)

  cond_name : Symbols.macro;
  (** condition macro in this execution model *)

  rec_ty : Type.ty;
  (** type along which the execution takes place (actions, integers, ...) *)
  
  macros : (Symbols.macro * general_macro_data) list
  (** definitions of the execution model macros *)
}

val define_execution_models : Symbols.table -> Symbols.table

val builtin_exec_models : Symbols.table -> exec_model_def list

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
  exec_model ->
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
(** [get_definition context macro ~args ~ts] returns the expansion of
    [macro(args)] at [ts], if the macro can be expanded.
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
    [get_dummy_definition table se m ~args:li] returns a term which resembles
    the one that would be obtained with [get_definition m li ts] for some [ts],
    except that it will feature meaningless action names in some places. *)
val get_dummy_definition :
  Symbols.table -> SE.fset -> Term.msymb -> args:Term.term list -> Term.term

(*------------------------------------------------------------------*)
type system_map_arg =
  | ADescr  of Action.descr 
  | AGlobal of { is : Vars.vars; ts : Vars.var;
                 ac_descrs : Action.descr list; inputs : Vars.vars }
  (** ac_descrs is the list of actions that have a shape where the macro
      is defined *)

(*------------------------------------------------------------------*)
type global_data

(** Given the name [ns] of a macro as well as a function [f] over
    terms, an [old_single_system] and a [new_single_system], takes the
    existing definition of [ns] in the old system, applies [f] to the
    existing definition, and update the value of [ns] accordingly in
    the new system. *)
val update_global_data :
  Symbols.table -> 
  Symbols.macro -> 
  System.Single.t ->
  System.Single.t ->
  (system_map_arg -> Symbols.macro -> Term.term -> Term.term) -> 
  Symbols.table

val as_global_macro : Symbols.data -> global_data

(** The global macro [m] is defined at any action which has
    the action shape as a strict or large prefix *)
val global_defined_from :
  Symbols.table -> Symbols.macro -> [`Strict | `Large] * Action.shape

(*------------------------------------------------------------------*)
(** {2 Utilities} *)

(** Get the ftype of a macro. 
    The second argument is the type of the variable we are recursing
    upon (i.e. the variable after the `@` *)
val fty : Symbols.table -> Symbols.macro -> Type.ftype * Type.ty 

val is_global : Symbols.table -> Symbols.macro -> bool

(** find the smallest prefix of [action] that is a suffix of
    [suffix] *)
val smallest_prefix :
  [`Large | `Strict] ->
  'a Action.t -> 'b Action.t -> 'b Action.t 

(*------------------------------------------------------------------*)
val _pp    : global_data formatter_p
val pp     : global_data formatter
val pp_dbg : global_data formatter
