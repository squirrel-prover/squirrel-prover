open Utils

(*------------------------------------------------------------------*)
type t = string

let from_string x : t = x

let to_string x : string = x

let pp fmt (x : t)  = Fmt.string fmt x
let pp_list fmt (l : t list) = Fmt.list ~sep:Fmt.comma pp fmt l

let left  = "left"
let right = "right"

(*------------------------------------------------------------------*)
module S = Ss 
module M = Ms

(*------------------------------------------------------------------*)
type renaming = {
  dst_labels : t list; 
  (** labels of [dst] *)
  map : (t * t) list; 
  (** map from [dst] labels to [src] labels *)
}

let pp_renaming fmt (r : renaming) =
  Fmt.pf fmt "@[<v 0>dst_labels: @[%a@]@;map: @[%a@]@]"
    (Fmt.list Fmt.string) r.dst_labels
    (Fmt.list (fun fmt (p,q) -> Fmt.pf fmt "%s ↦ %s" p q)) r.map
