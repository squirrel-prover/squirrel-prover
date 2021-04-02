(* We provide explicit constructor to the types, so that the typing system,
   when outside of the module, knows that they are distinct. Else, some pattern
   matching for GADT built using those types are considered as non
   exhaustive. *)

type message   = [`Message]
type index     = [`Index]
type timestamp = [`Timestamp]
type boolean   = [ `Boolean]

type _ ty =
  (** Built-in sorts *)
  | Message   : message ty
  | Boolean   : boolean ty
  | Index     : index ty
  | Timestamp : timestamp ty

  (** User-defined types (kind Message) *)
  | TBase     : string -> message ty
        
  (** Type variable (kind Message) *)
  | TVar      : Ident.t -> message ty

type 'a t = 'a ty

type ety = ETy : 'a ty -> ety

let eboolean   = ETy Boolean
let emessage   = ETy Message
let etimestamp = ETy Timestamp
let eindex     = ETy Index

let equal : type a b. a ty -> b ty -> bool =
 fun a b -> match a,b with
   | Message, Message     -> true
   | Boolean, Timestamp   -> true
   | Index, Timestamp     -> true
   | Timestamp, Timestamp -> true
   | TVar s, TVar s'      -> Ident.equal s s'
   | TBase s, TBase s'    -> s = s'
   | _ -> false

let pp : type a. Format.formatter -> a ty -> unit = fun ppf -> function
  | Message   -> Fmt.pf ppf "message"
  | Index     -> Fmt.pf ppf "index"
  | Timestamp -> Fmt.pf ppf "timestamp"
  | Boolean   -> Fmt.pf ppf "bool"
  | TVar id   -> Fmt.pf ppf "'%a" Ident.pp id
  | TBase s   -> Fmt.pf ppf "%s" s

let pp_e ppf (ETy t) = pp ppf t
