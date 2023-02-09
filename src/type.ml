open Utils

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

let pp_univar fmt u = Fmt.pf fmt "'_%a" Ident.pp_full u
  
(*------------------------------------------------------------------*)
(** Types of terms *)
type ty =
  | Message
  | Boolean
  | Index  
  | Timestamp
    
  | TBase of string
  (** User-defined types *)
        
  | TVar of tvar
  (** Type variable *)

  | TUnivar of univar
  (** Type unification variable *)

  | Tuple of ty list
  | Fun of ty * ty

(*------------------------------------------------------------------*)
let tboolean   = Boolean
let tmessage   = Message
let ttimestamp = Timestamp
let tindex     = Index

let base s   = TBase s

let rec fun_l tys tyout : ty =
  match tys with
  | [] -> tyout
  | ty :: tys -> Fun (ty, fun_l tys tyout)

(*------------------------------------------------------------------*)
(** Not exported *)
exception DestrFailed

let rec destr_funs t i =
  match t, i with
  | _, 0 -> [], t
  | Fun (t1, t2), _ -> 
    let lty, tout = destr_funs t2 (i - 1) in
    t1 :: lty, tout
  | _ -> raise DestrFailed

let destr_funs_opt t i =  
  try Some (destr_funs t i) with DestrFailed -> None

(*------------------------------------------------------------------*)
let rec decompose_funs t =
  match t with
  | Fun (t1, t2) -> 
    let lty, tout = decompose_funs t2 in
    t1 :: lty, tout
  | _ -> [], t

(*------------------------------------------------------------------*)
let tuple = function
  | [] -> assert false
  | [t] -> t
  | l -> Tuple l
           
(*------------------------------------------------------------------*)
(** Equality relation *)
let rec equal (a : ty) (b : ty) : bool =
  match a,b with
   | Boolean,   Boolean   -> true
   | Index,     Index     -> true
   | Timestamp, Timestamp -> true
   | Message,   Message   -> true
                               
   | TVar s, TVar s'  -> Ident.equal s s'

   | TBase s, TBase s' -> s = s'

   | TUnivar u, TUnivar u' -> Ident.equal u u'

   | Tuple tys1, Tuple tys2 -> 
     List.length tys1 = List.length tys2 &&
     List.for_all2 equal tys1 tys2

   | Fun (t1, t2), Fun (t1', t2') -> equal t1 t1' && equal t2 t2'
     
   | _ -> false

(*------------------------------------------------------------------*)
let rec pp (ppf : Format.formatter) : ty -> unit = function
  | Message   -> Fmt.pf ppf "message"
  | Index     -> Fmt.pf ppf "index"
  | Timestamp -> Fmt.pf ppf "timestamp"
  | Boolean   -> Fmt.pf ppf "bool"
  | TBase s   -> Fmt.pf ppf "%s" s
  | TVar id   -> pp_tvar ppf id
  | TUnivar u -> pp_univar ppf u

  | Tuple tys -> Fmt.list ~sep:(Fmt.any " * ") pp ppf tys

  | Fun (t1, t2) ->
    Fmt.pf ppf "%a -> %a" pp_chain_left t1 pp t2

and pp_chain_left ppf (t : ty) : unit =
  match t with
  | Fun (_, _) -> Fmt.pf ppf "(%a)" pp t
  | _          -> Fmt.pf ppf "%a"   pp t

(*------------------------------------------------------------------*)
let is_tuni = function TUnivar _ -> true | _ -> false
  
(*------------------------------------------------------------------*)
(** {2 Function symbols type} *)

(** Type of a function symbol: 
    ∀'a₁ ... 'aₙ, τ₁ → ... → τₙ → τ 

    Invariant: [fty_out] tvars and univars must be bounded by [fty_vars].
*)
type 'a ftype_g = {
  fty_vars : 'a list; (** 'a₁ ... 'aₙ *)  
  fty_args : ty list; (** τ₁, ... ,τₙ *)
  fty_out  : ty;      (** τ *)
}

(** A [ftype] uses [tvar] for quantified type variables. *)
type ftype = tvar ftype_g

(** An opened [ftype], using [univar] for quantified type varibales *)
type ftype_op = univar ftype_g

(*------------------------------------------------------------------*)
let pp_ftype_g pp_g fmt fty =
  let pp_args fmt args =
    if args = [] then () else
      Fmt.pf fmt "%a -> "
        (Fmt.list ~sep:(Fmt.any " ->@ ") pp) args
  in
  if fty.fty_vars = [] then
    Fmt.pf fmt "@[<hov 2>%a%a@]"
      pp_args fty.fty_args
      pp fty.fty_out
  else
    Fmt.pf fmt "@[<hov 2>[%a] %a%a@]"
      (Fmt.list ~sep:Fmt.comma pp_g) fty.fty_vars
      pp_args fty.fty_args
      pp fty.fty_out
    
let pp_ftype    = pp_ftype_g pp_univar
let pp_ftype_op = pp_ftype_g pp_tvar

(*------------------------------------------------------------------*)
let mk_ftype vars args out : ftype = {
  fty_vars = vars;
  fty_args = args;
  fty_out  = out;
}

let mk_ftype_tuple vars args out : ftype =
  match args with
  | [] | [_] -> mk_ftype vars args out
         
  (* arity ≥ 2 *)
  | _ -> mk_ftype vars [tuple args] out

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
  
let rec tsubst (s : tsubst) (t : ty) : ty = 
  match t with
  | Message   -> Message
  | Boolean   -> Boolean
  | Index     -> Index
  | Timestamp -> Timestamp

  | TBase str -> TBase str

  | TVar id -> Mid.find_dflt t id s.ts_tvar

  | TUnivar ui -> Mid.find_dflt t ui s.ts_univar

  | Tuple tys -> Tuple (List.map (tsubst s) tys)
  | Fun (t1, t2) -> Fun (tsubst s t1, tsubst s t2)

(*------------------------------------------------------------------*)
(** {2 Type inference } *)

(** Stateful API *)
module Infer : sig
  type env

  val pp : Format.formatter -> env -> unit

  val mk_env : unit -> env
    
  val mk_univar : env -> univar

  val open_tvars : env -> tvars -> univars * tsubst

  val norm   : env -> ty  -> ty
                         
  val unify_eq  : env -> ty -> ty -> [`Fail | `Ok]
  val unify_leq : env -> ty -> ty -> [`Fail | `Ok]

  val is_closed     : env -> bool
  val close         : env -> tsubst
  val gen_and_close : env -> tvars * tsubst
end = struct
  module Mid = Ident.Mid
                 
  (* an unification environment *)
  type env = ty Mid.t ref

  let pp fmt (e : env) =
    Fmt.pf fmt "[@[<v 0>%a@]]"
      (Fmt.list ~sep:Fmt.cut
         (fun fmt (id, ty) ->
            Fmt.pf fmt "@[<hv 2>@[%a@] →@ @[%a@]@]" Ident.pp id pp ty
      )) (Mid.bindings !e)

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
      let u' = Mid.find_dflt t u !env in
      if t = u' then u' else norm env u'

    | Fun (t1, t2) -> Fun (norm env t1, norm env t2)
      
    | Tuple l -> Tuple (List.map (norm env) l)
                   
    | Message | Boolean | Index | Timestamp | TBase _ | TVar _ -> t

  let norm_env (env : env) : unit = 
    env := Mid.map (norm env) !env

  (** An type inference environment is closed if every unification variable
       normal form is a univar-free type. *)
  let is_closed (env : env) : bool =
    let rec check = function
      | TUnivar _ -> false
      | Message | Boolean | Index | Timestamp | TBase _ | TVar _ -> true
      | Fun (t1, t2) -> check t1 && check t2
      | Tuple l -> List.for_all check l
    in
    
    norm_env env;
    Mid.for_all (fun _ -> check) !env

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
    let rec gen0 (gen_tvars, ts_univar) ty =
      match ty with
      | TUnivar uid -> 
        let tv = Ident.fresh uid in
        ( tv :: gen_tvars, 
          Mid.add uid (TVar tv) ts_univar )

      | Tuple l -> List.fold_left gen0 (gen_tvars, ts_univar) l

      | Fun (t1, t2) -> gen0 (gen0 (gen_tvars, ts_univar) t1) t2
          
      | TVar _ | TBase _
      | Message | Boolean | Timestamp | Index ->
        gen_tvars, ts_univar
    in
    let gen acc ty = gen0 acc (norm env ty) in
    
    let gen_tvars, ts_univar = 
      Mid.fold (fun _ ty acc -> gen acc ty) !env ([], Mid.empty)
    in
    let ts = { ts_univar; ts_tvar = Mid.empty; } in
    env := Mid.map (tsubst ts) !env;

    (* close the resulting environment *)
    gen_tvars, close env

  let unify_eq (env : env) (t : ty) (t' : ty) : [`Fail | `Ok] =
    let t  = norm env t
    and t' = norm env t' in

    let rec do_unif t t' : bool =
      let t, t' = if compare t t' < 0 then t', t else t, t' in

      if equal t t'
      then true
      else match t, t' with
        | TUnivar u, _ -> env := Mid.add u t' !env; true
        | Tuple tl, Tuple tl' ->
          List.length tl = List.length tl' &&
          do_unifs tl tl'

        | Fun (t1, t2), Fun (t1', t2') ->
          do_unifs [t1; t2] [t1'; t2']

        | _ -> false

    and do_unifs l l' = List.for_all2 do_unif l l' in
    
    if do_unif t t' then `Ok else `Fail
  
  (* FEATURE: subtype: improve type inference by not handling
     subtyping constraint as type equality constraints. *)
  let unify_leq env (t : ty) (t' : ty) : [`Fail | `Ok] =
    unify_eq env t t'
end


(*------------------------------------------------------------------*)
(** {2 Freshen function types} *)

let open_ftype (ty_env : Infer.env) (fty : ftype) : ftype_op =
  let vars_f, ts = Infer.open_tvars ty_env fty.fty_vars in

  (* compute the new function type *)
  { fty_vars = vars_f;
    fty_args = List.map (tsubst ts) fty.fty_args;
    fty_out  = tsubst ts fty.fty_out; }
  
