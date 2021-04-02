(* We provide explicit constructor to the types, so that the typing system,
   when outside of the module, knows that they are distinct. Else, some pattern
   matching for GADT built using those types are considered as non
   exhaustive. *)

type message   = [`Message]
type index     = [`Index]
type timestamp = [`Timestamp]
type boolean   = [`Boolean]
type unknown   = [`Unknown]

(*------------------------------------------------------------------*)
(** Kinds of types *)
type _ kind =
  | KMessage   : message   kind
  | KBoolean   : boolean   kind
  | KIndex     : index     kind
  | KTimestamp : timestamp kind
  | KUnknown   : unknown   kind (* for type inference variable *)

(*------------------------------------------------------------------*)
(** Variable for type inference *)
type univar = Ident.t

let pp_univar fmt u = Fmt.pf fmt "'_%a" Ident.pp u
    
(*------------------------------------------------------------------*)
(** Types of terms *)
type _ ty =
  (** Built-in types *)
  | Message   : message   ty
  | Boolean   : boolean   ty
  | Index     : index     ty
  | Timestamp : timestamp ty

  (** User-defined types *)
  | TBase   : string  -> message ty
        
  (** Type variable *)
  | TVar    : Ident.t -> message ty

  (** Type unification variable *)
  | TUnivar : univar  -> unknown ty

(*------------------------------------------------------------------*)
type 'a t = 'a ty

type ety = ETy : 'a ty -> ety

let eboolean   = ETy Boolean
let emessage   = ETy Message
let etimestamp = ETy Timestamp
let eindex     = ETy Index

let ebase s   = ETy (TBase s)
let eindex id = ETy (TVar id)

(*------------------------------------------------------------------*)
let kind : type a. a ty -> a kind = function
  | Boolean   -> KBoolean
  | Index     -> KIndex
  | Timestamp -> KTimestamp
  | TVar _    -> KMessage
  | TBase _   -> KMessage
  | Message   -> KMessage
  | TUnivar u -> KUnknown
  
(*------------------------------------------------------------------*)
(** Equality witness for kinds *)
type (_,_) kind_eq = Kind_eq : ('a, 'a) kind_eq

(** Equality witness for types *)
type (_,_) type_eq = Type_eq : ('a, 'a) type_eq

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

   | TUnivar u, TUnivar u' when Ident.equal u u' ->
     Some Type_eq
     
   | _ -> None

let equal : type a b. a ty -> b ty -> bool =
  fun a b -> equal_w a b <> None


(*------------------------------------------------------------------*)
(** Sub-typing relation, and return a (Ocaml) type equality witness *)
let subtype_w : type a b. a ty -> b ty -> (a,b) type_eq option =
  fun a b -> match equal_w a b with
    | Some Type_eq -> Some Type_eq
    | None -> match a, b with
      | TVar  _ , Message -> Some Type_eq
      | TBase _,  Message -> Some Type_eq 
                               
      | _ -> None

let subtype : type a b. a ty -> b ty -> bool =
  fun a b -> subtype_w a b <> None 

(*------------------------------------------------------------------*)
let pp : type a. Format.formatter -> a ty -> unit = fun ppf -> function
  | Message   -> Fmt.pf ppf "message"
  | Index     -> Fmt.pf ppf "index"
  | Timestamp -> Fmt.pf ppf "timestamp"
  | Boolean   -> Fmt.pf ppf "bool"
  | TVar id   -> Fmt.pf ppf "'%a" Ident.pp id
  | TBase s   -> Fmt.pf ppf "%s" s
  | TUnivar u -> pp_univar ppf u

let pp_e ppf (ETy t) = pp ppf t


(*------------------------------------------------------------------*)
(** {2 Function symbols type} *)

(** Type of a function symbol of index arity i: 
    ∀'a₁ ... 'aₙ, τ₁ × ... × τₙ → τ 

    Note that there is not unicity of the representation of a type using 
    an [ftype].
*)
type ftype = {
  fty_iarr : int;          (** i *)
  fty_vars : Ident.t list; (** a₁ ... 'aₙ *)  
  fty_args : ety list;     (** τ₁ × ... × τₙ *)
  fty_out  : ety;          (** τ *)
}

let mk_ftype iarr vars args out = {
  fty_iarr = iarr;
  fty_vars = vars;
  fty_args = args;
  fty_out  = out;
}

(*------------------------------------------------------------------*)
(** {2 Type inference } *)

module Infer : sig
  type env

  val mk_env : unit -> env
    
  val mk_univar : env -> ety * env
                         
  val unify_eq  : env -> ety -> ety -> env option
  val unify_leq : env -> ety -> ety -> env option
end = struct
  module Mid = Ident.Mid
                 
  (* an unification environment *)
  type env = ety Mid.t
      
  let mk_env () = Mid.empty

  let mk_univar env =
    let uv = Ident.create "u" in
    let ety = ETy (TUnivar uv) in
    ety, Mid.add uv ety env

  (* Univar are maximal for this ordering *)
  let compare : type a b. a ty -> b ty -> int =
    fun t t' -> match t, t' with
      | TUnivar u, TUnivar u' -> Ident.compare u u'
      | TUnivar _, _ -> 1
      | _, TUnivar _ -> -1
      | _, _ -> Stdlib.compare (ETy t) (ETy t')

  let compare_e et et' = match et, et' with
    | ETy t, ETy t' -> compare t t'
    
  let rec norm : type a. env -> a ty -> ety =
    fun env t ->
    match t with
    | TUnivar u ->
      let u' = Mid.find u env in
      if ETy t = u' then u' else norm_e env u'        
    | _ -> ETy t

  and norm_e env ety = match ety with
    | ETy t -> norm env t

  let unify_eq env (et : ety) (et' : ety) =
    let et  = norm_e env et
    and et' = norm_e env et' in

    let et, et' = if compare_e et et' < 0 then et', et else et, et' in
    
    match et, et' with
    | ETy t, ETy t' when equal t t'-> Some env
    | ETy t, ETy t' ->
      match t, t' with
      | TUnivar u, _ -> Some (Mid.add u et' env)
      | _ -> None

  (* TODO: improve type inference by not handling subtyping constraint as
     type equality constraints. *)
  let unify_leq env (et : ety) (et' : ety) = unify_eq env et et'
end
