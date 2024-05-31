module L = Location

(*------------------------------------------------------------------*)
(** Not type safe, do not export.
    [np] is the namespace path, [s] the symbol name. *)
let get_fsymb (p : Symbols.s_path) : Symbols.fname =
  Symbols.Operator.of_s_path p 

module Basic = struct

  let check_load table =
    if not (Symbols.Import.mem_sp ([], "Basic") table) then
      Tactics.hard_failure (Failure "theory Basic is not loaded")
        
  let get_fsymb table s =
    check_load table;
    get_fsymb ([],s)

  let fs_mem table = get_fsymb table "mem"
  let fs_add table = get_fsymb table "add"
  let const_emptyset table = get_fsymb table "empty_set"

  
end  
