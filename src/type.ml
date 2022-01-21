(** Kinds of types *)
type kind =
  | KMessage
  | KIndex  
  | KTimestamp

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
type ty =
  (** Built-in types *)
  | Message
  | Boolean
  | Index  
  | Timestamp

  (** User-defined types *)
  | TBase   of string
        
  (** Type variable *)
  | TVar    of tvar  

  (** Type unification variable *)
  | TUnivar of univar

(*------------------------------------------------------------------*)
(** Higher-order *)
type hty = Lambda of ty list * ty

(*------------------------------------------------------------------*)
let tboolean   = Boolean
let tmessage   = Message
let ttimestamp = Timestamp
let tindex     = Index

let base s   = TBase s

(*------------------------------------------------------------------*)
let kind : ty -> kind = function
  | Boolean   -> KMessage
  | Index     -> KIndex
  | Timestamp -> KTimestamp

  | TVar _    -> KMessage
  | TBase _   -> KMessage
  | Message   -> KMessage
  | TUnivar u -> KMessage

(*------------------------------------------------------------------*)
(** Equality relation *)
let equal (a : ty) (b : ty) : bool =
  match a,b with
   | Boolean,   Boolean   -> true
   | Index,     Index     -> true
   | Timestamp, Timestamp -> true
   | Message,   Message   -> true
                               
   | TVar s, TVar s'  -> Ident.equal s s'

   | TBase s, TBase s' -> s = s'

   | TUnivar u, TUnivar u' -> Ident.equal u u'
     
   | _ -> false

let ht_equal ht ht' = match ht, ht' with
  | Lambda (es1, t1), Lambda (es2, t2) ->
    List.length es1 = List.length es2 &&
    List.for_all2 equal es1 es2 &&
    equal t1 t2

(*------------------------------------------------------------------*)
(** Sub-typing relation *)
let subtype (a : ty) (b : ty) : bool =
  equal a b ||
  begin 
    match a, b with
    | TVar  _ , Message -> true
    | TBase _,  Message -> true
    | _ -> false
  end

(*------------------------------------------------------------------*)
let pp (ppf : Format.formatter) : ty -> unit = function
  | Message   -> Fmt.pf ppf "message"
  | Index     -> Fmt.pf ppf "index"
  | Timestamp -> Fmt.pf ppf "timestamp"
  | Boolean   -> Fmt.pf ppf "bool"
  | TBase s   -> Fmt.pf ppf "%s" s
  | TVar id   -> pp_tvar ppf id
  | TUnivar u -> pp_univar ppf u

(*------------------------------------------------------------------*)
let pp_ht fmt ht = 
  let pp_seq fmt () = Fmt.pf fmt " * " in

  let pp_ets fmt (ets : ty list) =
    match ets with
    | [] -> Fmt.pf fmt "()"
    | [ety] -> pp fmt ety
    | _ -> Fmt.pf fmt "@[<hv 2>(%a)@]" (Fmt.list ~sep:pp_seq pp) ets 
  in
  match ht with
  | Lambda (ets, ty) -> 
    Fmt.pf fmt "@[<hv 2>fun %a ->@ %a@]" pp_ets ets pp ty


(*------------------------------------------------------------------*)
let pp_kind (ppf : Format.formatter) : kind -> unit = function
  | KMessage   -> Fmt.pf ppf "message"
  | KIndex     -> Fmt.pf ppf "index"
  | KTimestamp -> Fmt.pf ppf "timestamp"

(*------------------------------------------------------------------*)
(** {2 Function symbols type} *)

(** Type of a function symbol of index arity i: 
    ∀'a₁ ... 'aₙ, τ₁ × ... × τₙ → τ 

    Invariant: [fty_out] tvars and univars must be bounded by [fty_vars].
*)
type 'a ftype_g = {
  fty_iarr : int;     (** i *)
  fty_vars : 'a list; (** 'a₁ ... 'aₙ *)  
  fty_args : ty list; (** τ₁ × ... × τₙ *)
  fty_out  : ty;      (** τ *)
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
module Sid = Ident.Sid
               
(** A type substitution*)
type tsubst = {
  ts_univar : ty Ident.Mid.t;
  ts_tvar   : ty Ident.Mid.t;
}

let tsubst_empty =
  { ts_univar = Mid.empty;
    ts_tvar   = Mid.empty; }

let tsubst_add_tvar   s tv ty = { s with ts_tvar   = Mid.add tv ty s.ts_tvar; }
let tsubst_add_univar s tu ty = { s with ts_univar = Mid.add tu ty s.ts_univar; }
  
let tsubst (s : tsubst) (t : ty) : ty = 
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

let tsubst_ht (ts : tsubst) (ht : hty) : hty =
  match ht with
  | Lambda (vs, f) -> Lambda (List.map (tsubst ts) vs, tsubst ts f)

(*------------------------------------------------------------------*)
(** {2 Type inference } *)

(** Stateful API *)
module Infer : sig
  type env

  val mk_env : unit -> env
    
  val mk_univar : env -> univar

  val open_tvars : env -> tvars -> univars * tsubst

  val norm   : env -> ty  -> ty
  val htnorm : env -> hty -> hty
                         
  val unify_eq  : env -> ty -> ty -> [`Fail | `Ok]
  val unify_leq : env -> ty -> ty -> [`Fail | `Ok]

  val is_closed     : env -> bool
  val close         : env -> tsubst
  val gen_and_close : env -> tvars * tsubst
end = struct
  module Mid = Ident.Mid
                 
  (* an unification environment *)
  type env = ty Mid.t ref
 
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
  let compare (t : ty) (t' : ty) : int =
    match t, t' with
      | TUnivar u, TUnivar u' -> Ident.compare u u'
      | TUnivar _, _ -> 1
      | _, TUnivar _ -> -1
      | _, _ -> Stdlib.compare t t'
    
  let rec norm (env : env) (t : ty) : ty =
    match t with
    | TUnivar u ->
      let u' = Mid.find u !env in
      if t = u' then u' else norm env u'        
    | _ -> t

  let htnorm env ht = match ht with
    | Lambda (evs, ty) -> Lambda (List.map (norm env) evs, norm env ty)

  let norm_env (env : env) : unit = 
    env := Mid.map (norm env) !env

  (** An type inference environment is closed if every unification variable
       normal form is a univar-free type. *)
  let is_closed (env : env) : bool =
    norm_env env;
    Mid.for_all (fun _ ety -> match ety with
        | TUnivar _ -> false
        | _ -> true
      ) !env

  let close (env : env) : tsubst =
    assert (is_closed env);
    { ts_tvar   = Mid.empty;
      ts_univar = !env; }

  (** Generalize unification variables and close the unienv. *)
  let gen_and_close (env : env) : tvars * tsubst =
    (* find all univar that are unconstrained and generalize them.
       Compute: 
       - generalized tvars, 
       - substitution from univar to generalized tvars *)
    let gen_tvars, ts_univar = 
      Mid.fold (fun _ ty (gen_tvars, ts_univar) ->
          match norm env ty with
          | TUnivar uid -> 
            let tv = Ident.fresh uid in
            ( tv :: gen_tvars, 
              Mid.add uid (TVar tv) ts_univar )

          | _ -> gen_tvars, ts_univar
        ) !env ([], Mid.empty)
    in
    let ts = { ts_univar; ts_tvar = Mid.empty; } in
    env := Mid.map (tsubst ts) !env;

    (* close the resulting environment *)
    gen_tvars, close env

  let unify_eq (env : env) (t : ty) (t' : ty) : [`Fail | `Ok] =
    let t  = norm env t
    and t' = norm env t' in

    let t, t' = if compare t t' < 0 then t', t else t, t' in
    
    if equal t t'
    then `Ok
    else match t, t' with
      | TUnivar u, _ -> env := Mid.add u t' !env; `Ok
      | _ -> `Fail

  (* TODO: improve type inference by not handling subtyping constraint as
     type equality constraints. *)
  let unify_leq env (t : ty) (t' : ty) : [`Fail | `Ok] =
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
  
