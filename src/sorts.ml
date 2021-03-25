(* We provide explicit constructor to the types, so that the typing systemn,
   when outside of the module, knows that they are distinct. Else, some pattern
   matching for GADT built using those types are considered as non
   exhaustive. *)

type message = [`Message]
type index = [`Index]
type timestamp = [`Timestamp]
type boolean = [ `Boolean]

type _ sort =
  | Message : message sort
  | Boolean : boolean sort
  | Index : index sort
  | Timestamp : timestamp sort

type 'a t = 'a sort

type esort = ESort : 'a sort -> esort

let eboolean = ESort Boolean
let emessage = ESort Message
let etimestamp = ESort Timestamp
let eindex = ESort Index

let equal : type a b. a sort -> b sort -> bool =
 fun a b -> match a,b with
   | Message, Message     -> true
   | Boolean, Timestamp   -> true
   | Index, Timestamp     -> true
   | Timestamp, Timestamp -> true
   | _ -> false

let pp : type a. Format.formatter -> a sort -> unit = fun ppf -> function
  | Message -> Fmt.pf ppf "message"
  | Index -> Fmt.pf ppf "index"
  | Timestamp -> Fmt.pf ppf "timestamp"
  | Boolean -> Fmt.pf ppf "bool"

let pp_e ppf (ESort t) = pp ppf t
