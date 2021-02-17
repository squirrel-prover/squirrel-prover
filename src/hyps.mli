(** Generic hypotheses, used in trace and equivalence sequent. *)

module type Hyp = sig 
  type t 
  val pp_hyp : Format.formatter -> t -> unit
  val htrue : t
end

(*------------------------------------------------------------------*) 
module type S = sig
  type hyp 

  type ldecl

  type hyps

  val empty : hyps

  val is_hyp : hyp -> hyps -> bool
    
  val by_id   : Ident.t -> hyps -> hyp
  val by_name : string  -> hyps -> ldecl

  val hyp_by_name : string  -> hyps -> hyp
  val id_by_name  : string  -> hyps -> Ident.t

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

  val fold : (Ident.t -> hyp -> 'a -> 'a) -> hyps -> 'a -> 'a
    
  val pp_ldecl : ?dbg:bool -> Format.formatter -> ldecl -> unit
  val pps : ?dbg:bool -> Format.formatter -> hyps -> unit

end

(*------------------------------------------------------------------*) 
module Mk (Hyp : Hyp) : sig
  type hyp = Hyp.t

  type ldecl = Ident.t * hyp

  type hyps

  val empty : hyps

  val is_hyp : hyp -> hyps -> bool
    
  val by_id   : Ident.t -> hyps -> hyp
  val by_name : string  -> hyps -> ldecl

  val hyp_by_name : string  -> hyps -> hyp
  val id_by_name  : string  -> hyps -> Ident.t

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

  val fold : (Ident.t -> hyp -> 'a -> 'a) -> hyps -> 'a -> 'a
    
  val pp_ldecl : ?dbg:bool -> Format.formatter -> ldecl -> unit
  val pps : ?dbg:bool -> Format.formatter -> hyps -> unit
end

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type hyp_error =
  | HypAlreadyExists of string
  | HypUnknown of string
    
exception Hyp_error of hyp_error

val pp_hyp_error : Format.formatter -> hyp_error -> unit

val hyp_error : hyp_error -> 'a
