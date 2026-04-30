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
  dst_labels : [`Concrete of t list | `Abstract]; 
  (** labels of [dst] if it is concrete *)
  map : (t * t) list; 
  (** map from [dst] labels to [src] labels 
      (empty when [dst] is abstract) *)
}

let pp_renaming fmt (r : renaming) =
  match r.dst_labels with
  | `Abstract -> 
    assert (r.map = []); 
    Fmt.pf fmt "no renaming [abstract systems]"

  | `Concrete dst_labels ->
    Fmt.pf fmt "@[<v 0>dst_labels: @[%a@]@;map: @[%a@]@]"
      (Fmt.list Fmt.string) dst_labels
      (Fmt.list (fun fmt (p,q) -> Fmt.pf fmt "%s ↦ %s" p q)) r.map
