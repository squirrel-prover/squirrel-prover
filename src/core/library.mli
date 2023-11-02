(** This module allow to load symbols defined in Squirrel theories *)

module Basic : sig
  val check_load : Symbols.table -> unit
        
  val get_fsymb : Symbols.table -> string -> Symbols.fname

  val fs_mem : Symbols.table -> Symbols.fname
  val fs_add : Symbols.table -> Symbols.fname
  val  const_emptyset : Symbols.table -> Symbols.fname
end  
