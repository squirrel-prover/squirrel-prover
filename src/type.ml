(* We provide explicit constructor to the types, so that the typing system,
   when outside of the module, knows that they are distinct. Else, some pattern
   matching for GADT built using those types are considered as non
   exhaustive. *)

(*------------------------------------------------------------------*)
type message   = [`Message]
type index     = [`Index]
type timestamp = [`Timestamp]

(*------------------------------------------------------------------*)
(** Kinds of types *)
type _ kind =
  | KMessage   : message   kind
  | KIndex     : index     kind
  | KTimestamp : timestamp kind

type ekind = EKind : 'a kind -> ekind

(*------------------------------------------------------------------*)
(** Type variables *)

type tvar = Ident.t
type tvars = tvar list

let pp_tvar fmt id = Fmt.pf fmt "'%a" Ident.pp id

let mk_tvar s = Ident.create s
let ident_of_tvar id = id
  
(*------------------------------------------------------------------*)
(** Variable for type inference *)

type univar  = Ident.t
type univars = univar list

let pp_univar fmt u = Fmt.pf fmt "'_%a" Ident.pp u
  
(*------------------------------------------------------------------*)
(** Types of terms *)
type _ ty =
  (** Built-in types *)
  | Message   : message   ty
  | Boolean   : message   ty
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

(*------------------------------------------------------------------*)
type tmessage   = message   ty
type ttimestamp = timestamp ty
type tindex     = index     ty

(*------------------------------------------------------------------*)
(** Higher-order *)
type hty =
  | Lambda of ety list * tmessage 

(*------------------------------------------------------------------*)
let eboolean   = ETy Boolean
let emessage   = ETy Message
let etimestamp = ETy Timestamp
let eindex     = ETy Index

let ebase s   = ETy (TBase s)

(*------------------------------------------------------------------*)
let kind : type a. a ty -> a kind = function
  | Boolean   -> KMessage
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

let eequal (ETy t1) (ETy t2) = equal t1 t2

let ht_equal ht ht' = match ht, ht' with
  | Lambda (es1, t1), Lambda (es2, t2) ->
    List.length es1 = List.length es2 &&
    List.for_all2 eequal es1 es2 &&
    equal t1 t2

(*------------------------------------------------------------------*)
(** Equality relation, and return a (Ocaml) type equality witness *)
let equalk_w : type a b. a kind -> b kind -> (a,b) type_eq option =
 fun a b -> match a,b with
   | KIndex,     KIndex     -> Some Type_eq
   | KTimestamp, KTimestamp -> Some Type_eq
   | KMessage,   KMessage   -> Some Type_eq
     
   | _ -> None

let equalk : type a b. a kind -> b kind -> bool =
  fun a b -> equalk_w a b <> None

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
let pp_ht fmt ht = 
  let pp_seq fmt () = Fmt.pf fmt " * " in

  let pp_ets fmt (ets : ety list) =
    match ets with
    | [] -> Fmt.pf fmt "()"
    | [ety] -> pp_e fmt ety
    | _ -> Fmt.pf fmt "@[<hv 2>(%a)@]" (Fmt.list ~sep:pp_seq pp_e) ets 
  in
  match ht with
  | Lambda (ets, ty) -> 
    Fmt.pf fmt "@[<hv 2>fun %a ->@ %a@]" pp_ets ets pp ty


(*------------------------------------------------------------------*)
let pp_kind : type a. Format.formatter -> a kind -> unit = fun ppf -> function
  | KMessage   -> Fmt.pf ppf "message"
  | KIndex     -> Fmt.pf ppf "index"
  | KTimestamp -> Fmt.pf ppf "timestamp"

let pp_kinde ppf (EKind t) = pp_kind ppf t


(*------------------------------------------------------------------*)
(** {2 Function symbols type} *)

(** Type of a function symbol of index arity i: 
    ∀'a₁ ... 'aₙ, τ₁ × ... × τₙ → τ 

    Invariant: [fty_out] tvars and univars must be bounded by [fty_vars].
*)
type 'a ftype_g = {
  fty_iarr : int;             (** i *)
  fty_vars : 'a list;         (** 'a₁ ... 'aₙ *)  
  fty_args : message ty list; (** τ₁ × ... × τₙ *)
  fty_out  : message ty;      (** τ *)
}

(** A [ftype] uses [tvar] for quantified type variables. *)
type ftype = tvar ftype_g

(** An opened [ftype], using [univar] for quantified type varibales *)
type ftype_op = univar ftype_g

let mk_ftype iarr vars args out : ftype = {
  fty_iarr = iarr;
  fty_vars = vars;
  fty_args = args;
  fty_out  = out;
}

(*------------------------------------------------------------------*)
(** {2 Type substitution } *)

module Mid = Ident.Mid
               
(** A type substitution*)
type tsubst = {
  ts_univar : message ty Ident.Mid.t;
  ts_tvar   : message ty Ident.Mid.t;
}

let tsubst_empty =
  { ts_univar = Mid.empty;
    ts_tvar   = Mid.empty; }

let tsubst_add_tvar   s tv ty = { s with ts_tvar   = Mid.add tv ty s.ts_tvar; }
let tsubst_add_univar s tu ty = { s with ts_univar = Mid.add tu ty s.ts_univar; }
  
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

let tsubst_ht (ts : tsubst) (ht : hty) : hty =
  match ht with
  | Lambda (vs, f) -> Lambda (List.map (tsubst_e ts) vs, tsubst ts f)

(*------------------------------------------------------------------*)
(** {2 Type inference } *)

(** Stateful API *)
module Infer : sig
  type env

  val mk_env : unit -> env
    
  val mk_univar : env -> univar

  val open_tvars : env -> tvars -> univars * tsubst

  val norm   : env -> 'a ty -> 'a ty
  val enorm  : env ->   ety ->   ety
  val htnorm : env ->   hty ->   hty
                         
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
    uv

  let open_tvars ty_env tvars =
    let vars_f = List.map (fun _ ->
        mk_univar ty_env
      ) tvars in

    (* create substitution refreshing all type variables *)
    let ts_tvar =
      List.fold_left2 (fun ts_tvar id id_f ->        
          Mid.add id (TUnivar id_f) ts_tvar
        ) Mid.empty tvars vars_f
    in  
    let ts = { tsubst_empty with ts_tvar } in
    vars_f, ts


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

  let enorm env (ETy ty) = ETy (norm env ty)

  let htnorm env ht = match ht with
    | Lambda (evs, ty) -> Lambda (List.map (enorm env) evs, norm env ty)

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

    match equalk_w (kind t) (kind t') with
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


(*------------------------------------------------------------------*)
(** {2 Freshen function types} *)

let open_ftype (ty_env : Infer.env) (fty : ftype) : ftype_op =
  let vars_f, ts = Infer.open_tvars ty_env fty.fty_vars in

  (* compute the new function type *)
  { fty with fty_vars = vars_f;
             fty_args = List.map (tsubst ts) fty.fty_args;
             fty_out  = tsubst ts fty.fty_out; }
  
