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

(** [{ vars; pattern; when_cond; out }] corresponds to one possible
    expansion of a macro [m{se}@rec_var] when
    [∃ vars. rec_var = pattern && when_cond].

    [pattern = None] means that the check [rec_var = pattern] is
    always true (it corresponds to the pattern `_`).
   
    A body may thus have an additional free variable rec_var in
    [when_cond] and [out].  *)
type body = {
  vars      : Vars.vars;         (** The free variables of the pattern matching. *)
  pattern   : Term.term option;  (** The optional pattern *)
  when_cond : Term.term;         (** The condition *)
  out       : Term.term;         (** The output *)
}

(** Refresh the [var] field of a [body]. *) 
val refresh_body : body -> body 

val _pp_body    : body formatter_p
val pp_body     : body formatter
val pp_body_dbg : body formatter

(*------------------------------------------------------------------*)
(** Macros can be unfold according to some [rewriting_strategy], where:
    - [Exhaustive] means that the expansion of [m@tau] would always return
    the try find/if then else term summarizing all possibllities; 
    - [Exact] means that the macro is expanded only when a single
    possible expansion is found;
    - [Opaque] means that the macro is never expanded.
    
    This [rw_strategy] is used inside the Reduction module.
*)
type rw_strategy = Exhaustive | Exact |  Opaque

(*------------------------------------------------------------------*)
(** Restricts the single systems in which a macro [f] with bodies
    [bodies] is defined and can be used:

    - [Any]: explicit list of single systems.

    - [Like p]: in single systems compatible with [p].

    - [Systems t]: in all single systems of [t]. More precisely, if
      [t] is the system expression [{l1 ↦ p1, ..., ln ↦ pn}], then [f]
      is defined in the systems [p1,...,pn], and the body of [f] in
      system [pi] is given by looking at the projection [li] of [bodies].

      Invariant: we must have that the [pi]'s are all distincts labels.
*)
type in_systems =
  | Any 
  | Like of System.t
  | Systems of SE.t 

(*------------------------------------------------------------------*)
(** A macro with [name = m] is a recursive procedure defined in a given system [se] as:

    [let rec m x1 ... xn r =  
     match r with
     | r = pattern1   when when_cond1 => out1
     | ...
     | r = patternN   when when_condN => outN]

    where:
    - [params] is the list [x1,...,xn],
    - [match_param] is the recursive parameter [r],
    - [bodies] is the list of possible outputs under the given matching patterns
       and conditions,
    - all outputs must be of the same type [ty].

    Alternatively, the macro is defined as:
    [m{se} args @ t = 
         try find vars1 such that r=pattern1 && when_cond1 in 
            out1 
         else ... in
            outn
         else witness
    ]

    The patterns and conditions in [bodies] must be exhaustive and
    mutually exclusive (thus, the final else branch with [witness] is
    never taken). Formally, this can be written as:
    [(⋁_i ∃ varsi. match_param = patterni ∧ when_condi) ∧ 
      ⋀_i (∃ varsi. match_param = patterni ∧ when_cond_i → m{se}args@match_param=outi)]
*)
type structured_macro_data = {
  name                : Symbols.macro;        (** a macro [m] *)
  params              : Vars.vars;            (** the parameters of the macro *)
  dist_param          : Vars.var option;
  (** the (optional) distinguished parameter, which is used for the
      parameter we are matching or recursing upon *)
  bodies              : body list;            (** the list of possible expansions *)
  ty                  : Type.ty;              (** return type of [bodies] *)
  in_systems          : in_systems;
  (** the systems in which the macro is defined (see [in_systems]'s type definition) *)
  rw_strat            : rw_strategy;          (** the rewrite strategy of the macro *)
  info                : Term.macro_info;      (** macro information (for printing) *)
  decreasing_quantity : Term.term option;
  (** The quantity for which the (recursive) function terminates.
      A term of type 'a, with free variable dist_param.
      Is None unless manually specified by the user input.
  *)
  decreasing_measure  : Symbols.fname;
  (** the order over the quantity, which must well_founded.
      A term symbol of type fun : a'-> 'a -> bool.
      It always defaults to Library.Prelude.fs_lt *)   
}

(*------------------------------------------------------------------*)
val _pp_structured_macro_data    : structured_macro_data formatter_p
val pp_structured_macro_data     : structured_macro_data formatter
val pp_structured_macro_data_dbg : structured_macro_data formatter

(*------------------------------------------------------------------*)
(** [mk_term_of_bodies table bodies match_param] returns the term
    corresponding to all possibilities, using if then else/try
    finds. *)
val mk_term_of_bodies : Symbols.table -> body list -> Term.term -> Term.term
                                                                     
(*------------------------------------------------------------------*)
(** A general macro definition. *)
type general_macro_data =
  | Structured of structured_macro_data
  | ProtocolMacro of [`Output | `Cond]
  (** ad hoc macro definitions using action descriptions *)

(*------------------------------------------------------------------*)
type Symbols.general_macro_def += Macro_data of general_macro_data

(*------------------------------------------------------------------*)
val get_general_macro_data : Symbols.general_macro_def -> general_macro_data
val as_general_macro : Symbols.data -> general_macro_data

val get_rw_strat   : Symbols.table -> Term.msymb    -> rw_strategy
val get_macro_info : Symbols.table -> Symbols.macro -> Term.macro_info

(* For a call m@t, returns the corresponding decreasing quantity with its order. *)
val get_macro_deacreasing_info :
  Symbols.table -> Symbols.macro -> Term.term -> Term.term * Symbols.fname

val msymb : Symbols.table -> Symbols.macro -> Term.msymb

(*------------------------------------------------------------------*)
(** {2 Execution models} *)

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

(** The classical execution model uses the following macro definitions:

    [let rec frame@tau =  
       match tau with
       | _ when tau <> init && happens(tau) => 
          <frame@pred tau, 
          < of_bool(exec@tau), 
            if exec@tau then output@tau else 0 >>
       | init => zero
       | _ when not(happens(tau)) => empty]

    [let rec exec@tau =  
       match tau with
       | _ when tau <> init && happens(tau) => 
         exec@pred tau && cond@tau
       | init => true
       | _ when not(happens(tau)) => false]

    [let rec input@tau =  
       match tau with
       | _ when tau <> init && happens(tau) => 
           att(frame@pred tau)
       | init => empty
       | _ when not(happens(tau)) => empty]

    [let rec output/cond@tau =  
       match tau with
       | Action1 when happens Action1 => ...
       | ...
       | ActionN when happens ActionN => ...
       | _ when not(happens(tau)) => empty/false]

    [let rec state_of_Action@tau =  
       match tau with
       | Action1 when happens Action1 => ...
       | ...
       | ActionN when happens ActionN => ...
       | _ when(happens(tau)) => state_of_Action@pred(tau)
       | _ when not(happens(tau)) => empty/false]

    Further, global macros are used to encode process-level `let`
    definitions. These are described below.
*)


(*------------------------------------------------------------------*)
(** {2 Global macro definitions} *)

(** Declare a global macro (whose meaning is the same accross
    several actions, which is useful to model let-expressions)
    given a term abstracted over input variables, indices,
    and some timestamp.
    A fresh name is generated for the macro if needed.

    A global macro definition corresponds to the definition (non
    recursive):
      [let glob_of_Action@tau =  
         match tau with
         | Action => glob_of_action@Action
         | init   => witness]
*)
val declare_global :
  Symbols.table ->
  System.t ->
  Action.exec_model ->
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

(** A expand context:
    - [InSequent]: when in a sequent. Most common mode.
    - [InGlobal {inputs}]: when in a global macro definition.
      In that case, [inputs] are the inputs variables of the global
      macro we are doing the expansion in. *)
type expand_context = InSequent | InGlobal of { inputs : Vars.vars }

(*------------------------------------------------------------------*)
(** [unfol env m args rec_arg] unfolds the macro [m] with arguments
    [args] and the recursive argument [rec_arg] in system
    [env.system.set].

    The result is: 
    - [`Result ( body list)] if unfold could not
      trivially do the pattern match or remove some conditions, it then
      returns the exhaustive list of all bodies without instantiation.
    - also [`Result ( body list)] if unfold was able to perform some
      pattern matchings and thus instantiate some of the bodies.
    - [`Unknown] if it is impossible to give an exhaustive list of
      possibilities, e.g. for [output{any}@tau] (indeed, we do not know
      the definition of [output] in all possible systems).

    To note, the macro call must be well-typed, e.g. [output{se}@A]
    with [A] not an element of the possible timestamps of [se] is
    forbiden, as it is an ill-typed term that should never be
    produced/parsed.

    Whenever we have that:
    [unfold se table m args rec_arg = `Result (_, [l1; ...; ln])] 
    where
    [li = { varsi; patterni; when_condi; outi }] (as a record of type [body]), 
    then [l1; ...; ln] is an exhaustive description of the values that
    [m{se}args@match_param] may take:
    [(⋁_i ∃ varsi. rec_arg = patterni ∧ when_condi) ∧ 
     ⋀_i (∃ varsi. rec_arg = patterni ∧ when_cond_i → m{se}args@match_param=outi)]

    [li.varsi] must be the only new free variables in the corresponding body.
    
    If some pattern matchings suceeded, the correspondig [li] is
    simplified by taking
    [varsi={},patterni=None].

    For now, only basic forms of pattern-matching over constructors is
    supported.
*)
val unfold :
  ?expand_context:expand_context ->
  Env.t ->
  Term.msymb ->
  Term.term list ->
  Term.term ->
  [ `Results of body list | `Unknown ]


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

type rec_arg_ty = [`At of Type.ty | `Standard of Type.ty | `None]

(** Get the ftype of a macro.
    The second argument is the type of the variable we are recursing
    upon:
    - [`At]       : this the variable after the `@` for builtin symbols;
    - [`Standard] : this is the last argument of the macro;
    - [`None]     : the macro has no final argument.

    Note that this last argument is not part of the return ftype's
    arguments [fty_args]. *)
val fty : 
  Symbols.table -> Symbols.macro -> 
  Type.ftype * rec_arg_ty

val is_global : Symbols.table -> Symbols.macro -> bool

(** find the smallest prefix of [action] that is a suffix of
    [suffix] *)
val smallest_prefix :
  [`Large | `Strict] ->
  'a Action.t -> 'b Action.t -> 'b Action.t 

(*------------------------------------------------------------------*)
(** {3 Execution model macros } *)

module Classic : sig
  val out_ty   : Type.ty
  val cond_ty  : Type.ty
  val inp_ty   : Type.ty
  val frame_ty : Type.ty
  val exec_ty  : Type.ty

  val inp   : Term.msymb
  val out   : Term.msymb
  val frame : Term.msymb
  val cond  : Term.msymb
  val exec  : Term.msymb
end

module Quantum : sig
  val out_ty        : Type.ty
  val cond_ty       : Type.ty
  val inp_ty        : Type.ty
  val transcript_ty : Type.ty
  val state_ty      : Type.ty
  val frame_ty      : Type.ty
  val exec_ty       : Type.ty

  val inp        : Term.msymb
  val transcript : Term.msymb
  val out        : Term.msymb
  val frame      : Term.msymb
  val cond       : Term.msymb
  val exec       : Term.msymb
  val state      : Term.msymb
end

(*------------------------------------------------------------------*)
(** {3 Pretty-printers } *)

val _pp    : global_data formatter_p
val pp     : global_data formatter
val pp_dbg : global_data formatter
