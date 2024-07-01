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

  val fs_mem : Symbols.table -> Symbols.fname
  val fs_add : Symbols.table -> Symbols.fname
  val  const_emptyset : Symbols.table -> Symbols.fname
end  
