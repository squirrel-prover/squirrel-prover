(* We provide explicit constructor to the types, so that the typing system,
   when outside of the module, knows that they are distinct. Else, some pattern
   matching for GADT built using those types are considered as non
   exhaustive. *)

type message   = [`Message]
type index     = [`Index]
type timestamp = [`Timestamp]
type boolean   = [ `Boolean]

(*------------------------------------------------------------------*)
(** Types of terms *)
type _ ty =
  (** Built-in types *)
  | Message   : message   ty
  | Boolean   : boolean   ty
  | Index     : index     ty
  | Timestamp : timestamp ty

  (** User-defined types (kind Message) *)
  | TBase     : string -> message ty
        
  (** Type variable (kind Message) *)
  | TVar      : Ident.t -> message ty

(*------------------------------------------------------------------*)
type 'a t = 'a ty

type ety = ETy : 'a ty -> ety

let eboolean   = ETy Boolean
let emessage   = ETy Message
let etimestamp = ETy Timestamp
let eindex     = ETy Index

(*------------------------------------------------------------------*)
(** Kinds of types *)
type _ kind =
  | KMessage   : message   kind
  | KBoolean   : boolean   kind
  | KIndex     : index     kind
  | KTimestamp : timestamp kind

let kind : type a. a ty -> a kind = function
  | Boolean   -> KBoolean
  | Index     -> KIndex
  | Timestamp -> KTimestamp
  | TVar _    -> KMessage
  | TBase _   -> KMessage
  | Message   -> KMessage
  
(*------------------------------------------------------------------*)
(** Equality witness for kinds *)
type (_,_) kind_eq = Kind_eq : ('a, 'a) kind_eq

(** Equality witness for types *)
type (_,_) type_eq = Type_eq : ('a, 'a) type_eq

(*------------------------------------------------------------------*)
(** Sub-typing relation, and return a (Ocaml) type equality witness *)
let subtype_w : type a b. a ty -> b ty -> (a,b) type_eq option =
 fun a b -> match a,b with
   | Boolean,   Boolean   -> Some Type_eq
   | Index,     Index     -> Some Type_eq
   | Timestamp, Timestamp -> Some Type_eq
   | Message,   Message   -> Some Type_eq
                           
   | TVar  _ , Message -> Some Type_eq
   | TBase _,  Message -> Some Type_eq 

   | TVar s, TVar s' when Ident.equal s s' ->
     Some Type_eq

   | TBase s, TBase s' when s = s' ->
     Some Type_eq
            
   | _ -> None

let subtype : type a b. a ty -> b ty -> bool =
  fun a b -> subtype_w a b <> None 

(*------------------------------------------------------------------*)
(** Equality relation, and return a (Ocaml) type equality witness *)
let equal_w : type a b. a ty -> b ty -> (a,b) type_eq option =
 fun a b -> match a,b with
   | Boolean,   Boolean   -> Some Type_eq
   | Index,     Index     -> Some Type_eq
   | Timestamp, Timestamp -> Some Type_eq
   | Message,   Message   -> Some Type_eq
                               
   | TVar s, TVar s' when Ident.equal s s' ->
     Some Type_eq

   | TBase s, TBase s' when s = s' ->
     Some Type_eq

   | _ -> None

let equal : type a b. a ty -> b ty -> bool =
  fun a b -> equal_w a b <> None
             
(*------------------------------------------------------------------*)
let pp : type a. Format.formatter -> a ty -> unit = fun ppf -> function
  | Message   -> Fmt.pf ppf "message"
  | Index     -> Fmt.pf ppf "index"
  | Timestamp -> Fmt.pf ppf "timestamp"
  | Boolean   -> Fmt.pf ppf "bool"
  | TVar id   -> Fmt.pf ppf "'%a" Ident.pp id
  | TBase s   -> Fmt.pf ppf "%s" s

let pp_e ppf (ETy t) = pp ppf t
