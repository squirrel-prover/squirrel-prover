(* We provide explicit constructor to the types, so that the typing system,
   when outside of the module, knows that they are distinct. Else, some pattern
   matching for GADT built using those types are considered as non
   exhaustive. *)

(*------------------------------------------------------------------*)
type message   = [`Message]
type index     = [`Index]
type timestamp = [`Timestamp]
type boolean   = [`Boolean]

(*------------------------------------------------------------------*)
(** Kinds of types *)
type _ kind =
  | KMessage   : message   kind
  | KBoolean   : boolean   kind
  | KIndex     : index     kind
  | KTimestamp : timestamp kind

(*------------------------------------------------------------------*)
(** Type variables *)

type tvar = Ident.t

let pp_tvar fmt id = Fmt.pf fmt "'%a" Ident.pp id

let tvar_of_ident id = id
let ident_of_tvar id = id
  
(*------------------------------------------------------------------*)
(** Variable for type inference *)

type univar = Ident.t

let pp_univar fmt u = Fmt.pf fmt "'_%a" Ident.pp u

let univar_of_ident id = id
  
(*------------------------------------------------------------------*)
(** Types of terms *)
type _ ty =
  (** Built-in types *)
  | Message   : message   ty
  | Boolean   : boolean   ty
  | Index     : index     ty
  | Timestamp : timestamp ty

  (** User-defined types *)
  | TBase     : string -> message ty
        
  (** Type variable *)
  | TVar      : tvar   -> message ty

  (** Type unification variable *)
  | TUnivar   : univar -> message ty

(*------------------------------------------------------------------*)
type 'a t = 'a ty

type ety = ETy : 'a ty -> ety

let eboolean   = ETy Boolean
let emessage   = ETy Message
let etimestamp = ETy Timestamp
let eindex     = ETy Index

let ebase s   = ETy (TBase s)

(*------------------------------------------------------------------*)
let kind : type a. a ty -> a kind = function
  | Boolean   -> KBoolean
  | Index     -> KIndex
  | Timestamp -> KTimestamp

  | TVar _    -> KMessage
  | TBase _   -> KMessage
  | Message   -> KMessage
  | TUnivar u -> KMessage
  
(*------------------------------------------------------------------*)
(** Equality witness for types and kinds *)
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
(** Equality relation, and return a (Ocaml) type equality witness *)
let equalk_w : type a b. a kind -> b kind -> (a,b) type_eq option =
 fun a b -> match a,b with
   | KBoolean,   KBoolean   -> Some Type_eq
   | KIndex,     KIndex     -> Some Type_eq
   | KTimestamp, KTimestamp -> Some Type_eq
   | KMessage,   KMessage   -> Some Type_eq
     
   | _ -> None

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
  | TBase s   -> Fmt.pf ppf "%s" s
  | TVar id   -> pp_tvar ppf id
  | TUnivar u -> pp_univar ppf u

let pp_e ppf (ETy t) = pp ppf t


(*------------------------------------------------------------------*)
(** {2 Function symbols type} *)

(** Type of a function symbol of index arity i: 
    ∀'a₁ ... 'aₙ, τ₁ × ... × τₙ → τ 
*)
type ftype = {
  fty_iarr : int;             (** i *)
  fty_vars : univar list;     (** a₁ ... 'aₙ *)  
  fty_args : message ty list; (** τ₁ × ... × τₙ *)
  fty_out  : message ty;      (** τ *)
}

let mk_ftype iarr vars args out = {
  fty_iarr = iarr;
  fty_vars = vars;
  fty_args = args;
  fty_out  = out;
}

(*------------------------------------------------------------------*)
(** {2 Type substitution } *)

module Mid = Ident.Mid
               
(** A substitution from unification variables to (existential) types. *)
type tsubst = {
  ts_univar : message ty Ident.Mid.t;
  ts_tvar   : message ty Ident.Mid.t;
}

let tsubst_empty =
  { ts_univar = Mid.empty;
    ts_tvar   = Mid.empty; }
  
let tsubst : type a. tsubst -> a ty -> a ty = fun s t ->
  match t with
  | Message   -> Message
  | Boolean   -> Boolean
  | Index     -> Index
  | Timestamp -> Timestamp

  | TBase str -> TBase str

  | TVar id   ->
    begin
      try Mid.find id s.ts_tvar
      with Not_found -> t
    end

  | TUnivar ui ->
    begin
      try Mid.find ui s.ts_univar
      with Not_found -> t
    end

let tsubst_e s (ETy ty) = ETy (tsubst s ty)

(*------------------------------------------------------------------*)
(** {2 Freshen function types} *)

let freshen_ftype (fty : ftype) : ftype =
  let vars_f = List.map Ident.fresh fty.fty_vars in
  
  (* create substitution refreshing all type variables in [fty] *)
  let ts_univar =
    List.fold_left2 (fun ts_univar id id_f ->
        Mid.add id (TUnivar id_f) ts_univar
      ) Mid.empty fty.fty_vars vars_f
  in  
  let ts = { tsubst_empty with ts_univar } in

  (* compute the new function type *)
  { fty with fty_vars = vars_f;
             fty_args = List.map (tsubst ts) fty.fty_args;
             fty_out  = tsubst ts fty.fty_out; }
  
(*------------------------------------------------------------------*)
(** {2 Type inference } *)

(** Stateful API *)
module Infer : sig
  type env

  val mk_env : unit -> env
    
  val mk_univar : env -> message ty
                         
  val unify_eq  : env -> 'a ty -> 'b ty -> [`Fail | `Ok]
  val unify_leq : env -> 'a ty -> 'b ty -> [`Fail | `Ok]

  val is_closed : env -> bool
  val close : env -> tsubst
end = struct
  module Mid = Ident.Mid
                 
  (* an unification environment *)
  type env = message ty Mid.t ref
 
  let mk_env () = ref Mid.empty 

  let mk_univar (env : env) =
    let uv = Ident.create "u" in
    let ety = TUnivar uv in
    env := Mid.add uv ety !env;
    ety

  (* Univar are maximal for this ordering *)
  let compare : type a b. a ty -> b ty -> int =
    fun t t' -> match t, t' with
      | TUnivar u, TUnivar u' -> Ident.compare u u'
      | TUnivar _, _ -> 1
      | _, TUnivar _ -> -1
      | _, _ -> Stdlib.compare (ETy t) (ETy t')

  let compare_e et et' = match et, et' with
    | ETy t, ETy t' -> compare t t'
    
  let rec norm : type a. env -> a ty -> a ty =
    fun env t ->
    match t with
    | TUnivar u ->
      let u' = Mid.find u !env in
      if t = u' then u' else norm env u'        
    | _ -> t

  (** An type inference environment is closed if every unification variable
       normal form is a univar-free type. *)
  let is_closed (env : env) : bool =
    Mid.for_all (fun _ ety -> match norm env ety with
        | TUnivar _ -> false
        | _ -> true
      ) !env

  let close (env : env) : tsubst =
    assert (is_closed env);
    { ts_tvar   = Mid.empty;
      ts_univar = !env; }

  let unify_eq : type a b. env -> a ty -> b ty -> [`Fail | `Ok] =
    fun env t t' ->
    let t  = norm env t
    and t' = norm env t' in

    match equal_w t t' with
    | None -> `Fail
    | Some Type_eq ->
      let t, t' = if compare t t' < 0 then t', t else t, t' in

      if equal t t'
      then `Ok
      else match t, t' with
        | TUnivar u, _ -> env := Mid.add u t' !env; `Ok
        | _ -> `Fail

  (* TODO: improve type inference by not handling subtyping constraint as
     type equality constraints. *)
  let unify_leq env (t : 'a ty) (t' : 'b ty) : [`Fail | `Ok] =
    unify_eq env t t'
end

