type ident = {
  name : string;
  tag  : int;
}

type idents = ident list

type t = ident

(*------------------------------------------------------------------*)
let cpt = ref 0

let uniq () = incr cpt; !cpt
    
let create s = { name = s; tag = uniq (); }

let name id = id.name
let tag  id = id.tag

let fresh t = create (name t)

let tag_compare i i' = i'.tag - i.tag
  
let compare i i' =
  if i'.tag = i.tag then 0
  else match Stdlib.compare i i' with
    | 0 -> tag_compare i i'
    | c -> c
    
let hash i = i.tag

(*------------------------------------------------------------------*)
let pp ppf id = Fmt.pf ppf "%s" (name id)

let pp_full ppf id = Fmt.pf ppf "%s/%d" (name id) (tag id)

(*------------------------------------------------------------------*)
module I = struct
  type _t = t
  type t = _t
  let compare = compare
end

module Mid = Map.Make (I)
module Sid = Set.Make (I)
