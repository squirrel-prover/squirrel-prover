module L = Location

(*------------------------------------------------------------------*)
let get_fsymb table (s : string) : Symbols.fname =
  try Symbols.Function.of_lsymb (L.mk_loc L._dummy s) table with
  | Symbols.Error _ -> assert false

module Basic = struct

  let check_load table =
    if not (Symbols.Theory.mem "Basic" table) then
      Tactics.hard_failure (Failure "theory Basic is not loaded")
        
  let get_fsymb table s =
    check_load table;
    get_fsymb table s

  let fs_mem table = get_fsymb table "mem"
  let fs_add table = get_fsymb table "add"
  let const_emptyset table = get_fsymb table "empty_set"

  
end  
