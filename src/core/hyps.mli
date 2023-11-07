(** Generic proof-context, used in all kinds of sequents.
    Contains hypotheses and definitions (let binders).
    Named [Hyps] for legacy reasons. *)

module SE = SystemExpr
module Args = TacticsArgs
  
(*------------------------------------------------------------------*) 
(** Signature for hypothesis data-type. *)
module type Hyp = sig 
  type t 

  val pp_hyp     : Format.formatter -> t -> unit
  val pp_hyp_dbg : Format.formatter -> t -> unit
  val _pp_hyp    : dbg:bool -> ?context:SE.context -> Format.formatter -> t -> unit

  (** Chooses a name for a formula, depending on the formula shape. *)
  val choose_name : t -> string

  val htrue : t
end

(** The system expression plays two role, giving:
    - the multi-term arity of the definition 
    - the systems used to interpret the macros in the term *)
type def = SE.t * Term.term

(** Local declaration kind -- general constructor.
    Type argument ['hyp] will be instanciated by the type of hypotheses *)
type ('hyp,_) gkind =
  | Hyp : ('hyp, 'hyp) gkind
  | Def : ('hyp,  def) gkind
      
(** Local declaration content -- general constructor. *)
type 'a gldecl_cnt = 
  | LHyp of 'a     (** hypothesis, with its name *)                  
  | LDef of def    (** a defined variable (e.g. from a let binding *)

(*------------------------------------------------------------------*) 
module type S1 = sig
  (** Hypothesis *)
  type hyp 

  (** Local declaration kind *)
  type 'a kind = (hyp,'a) gkind

  (** Local declaration content *)
  type ldecl_cnt = hyp gldecl_cnt

  (** Local declaration content *)
  type ldecl = Ident.t * ldecl_cnt

  type hyps

  (*------------------------------------------------------------------*) 
  (** [by_id id s] returns the local declaration named [id] in [s]. *)
  val by_id   : Ident.t ->            hyps -> ldecl_cnt
  val by_id_k : Ident.t -> 'a kind -> hyps -> 'a

  (** Same as [by_id], but does a look-up by name and returns the full local 
      declaration. *)
  val by_name   : Theory.lsymb ->            hyps -> Ident.t * ldecl_cnt
  val by_name_k : Theory.lsymb -> 'a kind -> hyps -> Ident.t * 'a

  (*------------------------------------------------------------------*) 
  val fresh_id  : ?approx:bool -> string      -> hyps -> Ident.t
  val fresh_ids : ?approx:bool -> string list -> hyps -> Ident.t list

  (*------------------------------------------------------------------*) 
  val _add : force:bool -> Ident.t -> ldecl_cnt -> hyps -> Ident.t * hyps

  (** Adds a local declaration, and name it according to a naming pattern. *)
  val add : Args.naming_pat -> ldecl_cnt -> hyps -> hyps
  
  (** Same as [add], but also returns the ident of the new local declaration. *)
  val add_i : Args.naming_pat -> ldecl_cnt -> hyps -> Ident.t * hyps
  
  val add_i_list :
    (Args.naming_pat * ldecl_cnt) list -> hyps -> Ident.t list * hyps
  
  val add_list : (Args.naming_pat * ldecl_cnt) list -> hyps -> hyps

  (*------------------------------------------------------------------*)
  (** Find the first local declaration satisfying a predicate. *)
  val find_opt : (ldecl -> bool) -> hyps -> ldecl option
  val find_all : (ldecl -> bool) -> hyps -> ldecl list

  (** Exceptionless. *)
  val find_map : (ldecl -> 'a option) -> hyps -> 'a option

  (** Find if there exists a local declaration satisfying a predicate. *)
  val exists : (ldecl -> bool) -> hyps -> bool

  (** Removes a formula. *)
  val remove : Ident.t -> hyps -> hyps

  val filter : (ldecl -> bool) -> hyps -> hyps

  val to_list : hyps -> ldecl list

  (*------------------------------------------------------------------*)
  (** [mem_id id s] returns true if there is a local declaration with id [id] 
      in [s]. *)
  val mem_id : Ident.t -> hyps -> bool

  (** Same as [mem_id], but does a look-up by name. *)  
  val mem_name : string  -> hyps -> bool
    
  (*------------------------------------------------------------------*)  
  (** [is_hyp f s] returns true if the formula appears inside the hypotesis
      of the sequent [s].  *)
  val is_hyp : hyp -> hyps -> bool

  (*------------------------------------------------------------------*)
  val map : ?hyp:(hyp -> hyp) -> ?def:(def -> def) -> hyps -> hyps

  val mapi :
    ?hyp:(Ident.t -> hyp -> hyp) ->
    ?def:(Ident.t -> def -> def) ->
    hyps -> hyps

  (*------------------------------------------------------------------*)
  val filter_map :
    ?hyp:(Ident.t -> hyp -> hyp option) -> 
    ?def:(Ident.t -> def -> def option) -> 
    hyps -> hyps

  (*------------------------------------------------------------------*)
  val fold      : (Ident.t -> ldecl_cnt -> 'a -> 'a) -> hyps -> 'a -> 'a
  val fold_hyps : (Ident.t -> hyp       -> 'a -> 'a) -> hyps -> 'a -> 'a

  (*------------------------------------------------------------------*)
  (** Clear trivial hypotheses *)
  val clear_triv : hyps -> hyps

  (*------------------------------------------------------------------*)
  val pp_ldecl : ?dbg:bool -> ?context:SE.context -> Format.formatter -> ldecl -> unit

  val pp_hyp : Format.formatter -> hyp  -> unit

  val pp     : Format.formatter -> hyps -> unit
  val pp_dbg : Format.formatter -> hyps -> unit
  val _pp    : dbg:bool -> Format.formatter -> hyps -> unit
end

(*------------------------------------------------------------------*)
(** [S1] with [empty] *)
module type S = sig
  include S1
  val empty : hyps
  val _pp : dbg:bool -> ?context:SE.context -> Format.formatter -> hyps -> unit
end

(*------------------------------------------------------------------*)
(** Functor for building an implementation of contexts
    for a particular kind of hypotheses. *)
module Mk (Hyp : Hyp) : S with type hyp = Hyp.t


(*------------------------------------------------------------------*)
(** {2 Equiv Hyps} *)

module EquivHyps : S with type hyp = Equiv.form

(*------------------------------------------------------------------*)
(** {2 Trace Hyps} *)

module TraceHyps : S with type hyp = Equiv.any_form

val get_atoms_of_hyps  : TraceHyps.hyps -> Term.Lit.literals 
val get_message_atoms  : TraceHyps.hyps -> Term.Lit.xatom list 
val get_trace_literals : TraceHyps.hyps -> Term.Lit.literals 
val get_eq_atoms       : TraceHyps.hyps -> Term.Lit.xatom list

(*------------------------------------------------------------------*)
(** {2 Changing the context of a set of hypotheses} *)

(** Change the context interpreting some hypotheses.
    The new hypotheses are understood in the new context.
    The new context must be compatible with the old one.

    Returned hypotheses (understood wrt the new context)
    are logical consequences of the hypotheses given in argument
    (understood wrt its own context): some hypotheses will thus be dropped
    while others will be projected.

    The optional [update_local] function can be used to override the
    treatment of local hypotheses, i.e. to determine when they can be
    kept (possibly with modifications) or if they should be dropped. *)
val change_trace_hyps_context :
  ?update_local:(Term.term -> Term.term option) ->
  old_context:SE.context ->
  new_context:SE.context ->
  table:Symbols.table ->
  vars:Vars.env ->
  TraceHyps.hyps -> TraceHyps.hyps

(** Same for equivalence hypotheses. *)
val change_equiv_hyps_context :
  old_context:SE.context ->
  new_context:SE.context ->
  table:Symbols.table ->
  vars:Vars.env ->
  EquivHyps.hyps -> EquivHyps.hyps
