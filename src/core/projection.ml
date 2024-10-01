open Utils

(*------------------------------------------------------------------*)
type t = string

let from_string x : t = x

let to_string x : string = x

let pp fmt (x : t)  = Fmt.string fmt x
let pp_list fmt (l : t list) = Fmt.list ~sep:Fmt.comma pp fmt l

let left  = "left"
let right = "right"

module S = Ss 
module M = Ms
