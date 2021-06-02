(** Generic hypotheses, used in all kinds of sequents. *)

(** Signature for hypothesis data-type:
  * anything that can be printed and has some notion of
  * a [true] hypothesis. *)
module type Hyp = sig 
  type t 
  val pp_hyp : Format.formatter -> t -> unit
  val htrue : t
end

(** Signature for contexts of hypotheses. *)
module type S = sig
  type hyp 

  type ldecl = Ident.t * hyp

  type hyps

  val empty : hyps

  val is_hyp : hyp -> hyps -> bool
    
  val by_id   : Ident.t      -> hyps -> hyp
  val by_name : Theory.lsymb -> hyps -> ldecl

  val hyp_by_name : Theory.lsymb -> hyps -> hyp
  val id_by_name  : Theory.lsymb -> hyps -> Ident.t

  val fresh_id : string -> hyps -> Ident.t
  val fresh_ids : string list -> hyps -> Ident.t list
  
  val add : force:bool -> Ident.t -> hyp -> hyps -> Ident.t * hyps

  val find_opt : (Ident.t -> hyp -> bool) -> hyps -> ldecl option
  val find_all : (Ident.t -> hyp -> bool) -> hyps -> ldecl list

  val find_map : (Ident.t -> hyp -> 'a option) -> hyps -> 'a option
    
  val exists : (Ident.t -> hyp -> bool) -> hyps -> bool
    
  val remove : Ident.t -> hyps -> hyps

  val filter : (Ident.t -> hyp -> bool) -> hyps -> hyps

  val to_list : hyps -> ldecl list

  val mem_id   : Ident.t -> hyps -> bool
  val mem_name : string  -> hyps -> bool

  val map :  (hyp ->  hyp) -> hyps -> hyps
  val mapi : (Ident.t -> hyp ->  hyp) -> hyps -> hyps

  val fold : (Ident.t -> hyp -> 'a -> 'a) -> hyps -> 'a -> 'a
    
  val pp_ldecl : ?dbg:bool -> Format.formatter -> ldecl -> unit
  val pps : ?dbg:bool -> Format.formatter -> hyps -> unit

end

(** Functor for building an implementation of contexts
  * for a particular kind of hypotheses. *)
module Mk (Hyp : Hyp) : S with type hyp = Hyp.t


(** Signature for sequents with hypotheses. *)
module type HypsSeq = sig
  (** Hypothesis *)
  type hyp 

  (** Local declaration *)
  type ldecl = Ident.t * hyp

  type sequent

  (** Adds a hypothesis, and name it according to a naming pattern. *)
  val add   : TacticsArgs.naming_pat -> hyp -> sequent -> sequent

  (** Same as [add], but also returns the ident of the added hypothesis. *)
  val add_i : TacticsArgs.naming_pat -> hyp -> sequent -> Ident.t * sequent

  val add_i_list :
    (TacticsArgs.naming_pat * hyp) list -> sequent -> Ident.t list * sequent
  val add_list   : (TacticsArgs.naming_pat * hyp) list -> sequent -> sequent

  val pp_hyp   : Format.formatter -> 'a Term.term -> unit
  val pp_ldecl : ?dbg:bool -> Format.formatter -> ldecl -> unit

  val fresh_id  : ?approx:bool -> string -> sequent -> Ident.t
  val fresh_ids : ?approx:bool -> string list -> sequent -> Ident.t list

  (** [is_hyp f s] returns true if the formula appears inside the hypotesis
      of the sequent [s].  *)
  val is_hyp : hyp -> sequent -> bool

  (** [by_id id s] returns the hypothesis with id [id] in [s]. *)
  val by_id : Ident.t -> sequent -> hyp

  (** Same as [by_id], but does a look-up by name and returns the full local 
      declaration. *)
  val by_name : Theory.lsymb -> sequent -> ldecl

  (** [mem_id id s] returns true if there is an hypothesis with id [id] 
      in [s]. *)
  val mem_id : Ident.t -> sequent -> bool

  (** Same as [mem_id], but does a look-up by name. *)  
  val mem_name : string -> sequent -> bool

  val to_list : sequent -> ldecl list

  (** Find the first local declaration satisfying a predicate. *)
  val find_opt : (Ident.t -> hyp -> bool) -> sequent -> ldecl option

  (** Exceptionless. *)
  val find_map : (Ident.t -> hyp -> 'a option) -> sequent -> 'a option

  (** Find if there exists a local declaration satisfying a predicate. *)
  val exists : (Ident.t -> hyp -> bool) -> sequent -> bool

  val map : (hyp -> hyp) -> sequent -> sequent
  val mapi : (Ident.t -> hyp ->  hyp) -> sequent -> sequent

  (** Removes a formula. *)
  val remove : Ident.t -> sequent -> sequent

  val fold : (Ident.t -> hyp -> 'a -> 'a) -> sequent -> 'a -> 'a

  (** Clear trivial hypotheses and reload hypotheses *)
  val clear_triv : sequent -> sequent

  val pp     : Format.formatter -> sequent -> unit
  val pp_dbg : Format.formatter -> sequent -> unit
end
