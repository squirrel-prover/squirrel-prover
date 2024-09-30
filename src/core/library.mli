(** This module allow to load symbols defined in Squirrel theories *)


(*------------------------------------------------------------------*)
(** Constructors for symbols declared in the prelude. *)
module Prelude : sig
  val fs_witness : Symbols.fname
  val fs_zeroes  : Symbols.fname
  val fs_leq     : Symbols.fname

  val mk_witness : Symbols.table -> ty_arg:Type.ty -> Term.term
  val mk_zeroes  : Symbols.table -> Term.term -> Term.term

  val mk_leq     : Symbols.table -> Term.term -> Term.term -> Term.term
end

(*------------------------------------------------------------------*)
module Basic : sig
  val check_load : Symbols.table -> unit
  val get_fsymb : Symbols.table -> string -> Symbols.fname
  val fs_mem : Symbols.table -> Symbols.fname
  val fs_add : Symbols.table -> Symbols.fname
  val const_emptyset : Symbols.table -> Symbols.fname
end

module Real : sig
  val check_load : Symbols.table -> unit
  val get_fsymb : Symbols.table -> string -> Symbols.fname
  val get_btype : Symbols.table -> string -> Symbols.btype

  (*------------------------------------------------------------------*)
  val treal : Symbols.table -> Type.ty

  (*------------------------------------------------------------------*)
  val fs_add   : Symbols.table -> Symbols.fname
  val fs_minus : Symbols.table -> Symbols.fname
  val fs_opp   : Symbols.table -> Symbols.fname
 
  val fs_mul   : Symbols.table -> Symbols.fname
  val fs_div   : Symbols.table -> Symbols.fname
  val fs_inv   : Symbols.table -> Symbols.fname
 
  val fs_zero  : Symbols.table -> Symbols.fname
  val fs_one   : Symbols.table -> Symbols.fname
  val fs_two   : Symbols.table -> Symbols.fname

  (*------------------------------------------------------------------*)
  val mk_add   : Symbols.table -> Term.term -> Term.term -> Term.term
  val mk_minus : Symbols.table -> Term.term -> Term.term -> Term.term
  val mk_opp   : Symbols.table -> Term.term              -> Term.term

  val mk_mul   : Symbols.table -> Term.term -> Term.term -> Term.term
  val mk_div   : Symbols.table -> Term.term -> Term.term -> Term.term
  val mk_inv   : Symbols.table -> Term.term              -> Term.term

  val mk_zero  : Symbols.table                           -> Term.term
  val mk_one   : Symbols.table                           -> Term.term
  val mk_two   : Symbols.table                           -> Term.term
end
