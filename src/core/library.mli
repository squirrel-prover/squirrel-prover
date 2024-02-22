(** This module allow to load symbols defined in Squirrel theories *)


(*------------------------------------------------------------------*)
(** Constructors for symbols declared in the prelude. *)
module Prelude : sig
  val fs_witness : Symbols.fname
  val fs_zeroes  : Symbols.fname

  val mk_witness : Symbols.table -> ty_arg:Type.ty -> Term.term
  val mk_zeroes  : Symbols.table -> Term.term -> Term.term
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
  val real : Symbols.table -> Type.ty
  val leq : Symbols.table -> Symbols.fname
  val add : Symbols.table -> Symbols.fname
  val minus : Symbols.table -> Symbols.fname
  val zero : Symbols.table -> Symbols.fname
  val mk_minus : Symbols.table -> Term.term -> Term.term

  val mk_add :
    Symbols.table -> Term.term -> Term.term -> Term.term

  val mk_leq :
    Symbols.table -> Term.term -> Term.term -> Term.term

  val mk_zero : Symbols.table -> Term.term
end
