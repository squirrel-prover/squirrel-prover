(** Generic hypotheses, used in all kinds of sequents. *)


module Args = TacticsArgs
  
(*------------------------------------------------------------------*) 
(** Signature for hypothesis data-type. *)
module type Hyp = sig 
  type t 

  val pp_hyp     :             Format.formatter -> t -> unit
  val _pp_hyp    : dbg:bool -> Format.formatter -> t -> unit
  val pp_hyp_dbg :             Format.formatter -> t -> unit

  (** Chooses a name for a formula, depending on the formula shape. *)
  val choose_name : t -> string

  val htrue : t
end

(*------------------------------------------------------------------*) 
module type S1 = sig
  (** Hypothesis *)
  type hyp 

  (** Local declaration *)
  type ldecl = Ident.t * hyp

  type hyps

  (*------------------------------------------------------------------*) 
  (** [by_id id s] returns the hypothesis with id [id] in [s]. *)
  val by_id : Ident.t -> hyps -> hyp

  (** Same as [by_id], but does a look-up by name and returns the full local 
      declaration. *)
  val by_name : Theory.lsymb -> hyps -> ldecl

  (*------------------------------------------------------------------*) 
  val fresh_id  : ?approx:bool -> string      -> hyps -> Ident.t
  val fresh_ids : ?approx:bool -> string list -> hyps -> Ident.t list

  (*------------------------------------------------------------------*) 
  val _add : force:bool -> Ident.t -> hyp -> hyps -> Ident.t * hyps

  (** Adds a hypothesis, and name it according to a naming pattern. *)
  val add : Args.naming_pat -> hyp -> hyps -> hyps
  
  (** Same as [add], but also returns the ident of the added hypothesis. *)
  val add_i : Args.naming_pat -> hyp -> hyps -> Ident.t * hyps
  
  val add_i_list :
    (Args.naming_pat * hyp) list -> hyps -> Ident.t list * hyps
  
  val add_list   : (Args.naming_pat * hyp) list -> hyps -> hyps

  (*------------------------------------------------------------------*)
  (** Find the first local declaration satisfying a predicate. *)
  val find_opt : (Ident.t -> hyp -> bool) -> hyps -> ldecl option
  val find_all : (Ident.t -> hyp -> bool) -> hyps -> ldecl list

  (** Exceptionless. *)
  val find_map : (Ident.t -> hyp -> 'a option) -> hyps -> 'a option

  (** Find if there exists a local declaration satisfying a predicate. *)
  val exists : (Ident.t -> hyp -> bool) -> hyps -> bool

  (** Removes a formula. *)
  val remove : Ident.t -> hyps -> hyps

  val filter : (Ident.t -> hyp -> bool) -> hyps -> hyps

  val to_list : hyps -> ldecl list

  (*------------------------------------------------------------------*)
  (** [mem_id id s] returns true if there is an hypothesis with id [id] 
      in [s]. *)
  val mem_id : Ident.t -> hyps -> bool

  (** Same as [mem_id], but does a look-up by name. *)  
  val mem_name : string  -> hyps -> bool

  (*------------------------------------------------------------------*)  
  (** [is_hyp f s] returns true if the formula appears inside the hypotesis
      of the sequent [s].  *)
  val is_hyp : hyp -> hyps -> bool

  (*------------------------------------------------------------------*)
  val map  :  (hyp ->  hyp) -> hyps -> hyps
  val mapi :  (Ident.t -> hyp ->  hyp) -> hyps -> hyps

  val fold : (Ident.t -> hyp -> 'a -> 'a) -> hyps -> 'a -> 'a

  (*------------------------------------------------------------------*)
  (** Clear trivial hypotheses *)
  val clear_triv : hyps -> hyps

  (*------------------------------------------------------------------*)
  val pp_ldecl : ?dbg:bool -> Format.formatter -> ldecl -> unit

  val pp_hyp   : Format.formatter -> hyp  -> unit

  val pp       :             Format.formatter -> hyps -> unit
  val _pp      : dbg:bool -> Format.formatter -> hyps -> unit
  val pp_dbg   :             Format.formatter -> hyps -> unit
end

(*------------------------------------------------------------------*)
(** [S1] with [empty] *)
module type S = sig
  include S1
  val empty : hyps
end

(*------------------------------------------------------------------*)
(** Functor for building an implementation of contexts
  * for a particular kind of hypotheses. *)
module Mk (Hyp : Hyp) : S with type hyp = Hyp.t


(*------------------------------------------------------------------*)
(** {2 Trace Hyps} *)

module TraceHyps : S with type hyp = Equiv.any_form

val get_atoms_of_hyps  : TraceHyps.hyps -> Term.Lit.literals 
val get_message_atoms  : TraceHyps.hyps -> Term.Lit.xatom list 
val get_trace_literals : TraceHyps.hyps -> Term.Lit.literals 
val get_eq_atoms       : TraceHyps.hyps -> Term.Lit.xatom list 
