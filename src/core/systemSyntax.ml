open Utils

type t = Symbols.system

(*------------------------------------------------------------------*)
let convert table s = Symbols.System.convert_path s table

(*------------------------------------------------------------------*)
type error =
  | Shape_error
  | Invalid_projection

let pp_error fmt = function
  | Shape_error ->
    Format.fprintf fmt "cannot register a shape twice with distinct indices"
  | Invalid_projection ->
    Format.fprintf fmt "invalid projection"

exception Error of error

let error e = raise (Error e)

(*------------------------------------------------------------------*)
let store_compatible = ref None
let compatible table t1 t2 : bool = (oget !store_compatible) table t1 t2
let record_compatible 
    (f : Symbols.table -> t -> t -> bool) : unit 
  =
  store_compatible := Some f

(*------------------------------------------------------------------*)
(** Single systems *)

module Single = struct

  type t = {
    system     : Symbols.system ;
    projection : Projection.t
  }

  let make_unsafe system projection = { system; projection; }

  let pp fmt {system;projection} =
    if Projection.to_string projection = "ε" then
      (* Convention typically used for single system. *)
      Format.fprintf fmt "%a" Symbols.pp_path system
    else
      Format.fprintf fmt "%a/%a"
        Symbols.pp_path system
        Projection.pp projection

  let compare (s1 : t) (s2 : t) =
    Stdlib.compare
      (s1.system.id,s1.projection)
      (s2.system.id,s2.projection)

  module O = struct
    type _t =  t
    type  t = _t
    let compare = compare
  end

  module Map = Map.Make(O)
  module Set = Set.Make(O)
end
