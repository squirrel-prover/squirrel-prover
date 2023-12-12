open Utils

(*------------------------------------------------------------------*)
module Mid = Ident.Mid
module Sid = Ident.Sid

(*------------------------------------------------------------------*)
(** Type variables *)

type tvar = Ident.t
type tvars = tvar list

let _pp_tvar ~dbg fmt id = 
  if dbg then
    Fmt.pf fmt "'%a" Ident.pp_full id
  else 
    Fmt.pf fmt "'%a" Ident.pp id

let pp_tvar     = _pp_tvar ~dbg:false
let pp_tvar_dbg = _pp_tvar ~dbg:true

let mk_tvar s = Ident.create s
let ident_of_tvar id = id
  
(*------------------------------------------------------------------*)
(** Variable for type inference *)

type univar  = Ident.t
type univars = univar list

(* always debug printing *)
let pp_univar fmt u = Fmt.pf fmt "%a" Ident.pp_full u

let to_univar u = u

(*------------------------------------------------------------------*)
(** Free variables in types *)

module Fv = struct
  type t = { tv : Sid.t; uv : Sid.t; }
           
  let pp fmt t = 
    Fmt.pf fmt "@[<v 0>{ tv: @[%a@];@ uv: @[%a@] }@]" 
      (Fmt.list Ident.pp_full) (Sid.elements t.tv)
      (Fmt.list Ident.pp_full) (Sid.elements t.uv)

  let empty = { tv = Sid.empty; uv = Sid.empty; }

  let union t1 t2 = { 
    tv = Sid.union t1.tv t2.tv; 
    uv = Sid.union t1.uv t2.uv; 
  }

  let diff t1 t2 = { 
    tv = Sid.diff t1.tv t2.tv; 
    uv = Sid.diff t1.uv t2.uv; 
  }

  let add_tv tv t = { t with tv = Sid.add tv t.tv }
  let add_uv uv t = { t with uv = Sid.add uv t.uv }

  let rem_tv tv t = { t with tv = Sid.remove tv t.tv }
  let rem_uv tv t = { t with uv = Sid.remove tv t.uv }

  let rem_tvs tvs t = List.fold_left (fun t v -> rem_tv v t) t tvs 
  let rem_uvs uvs t = List.fold_left (fun t v -> rem_uv v t) t uvs
end

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
(** {2 Iterators, do not recurse} *)
           
let fold (f : ty -> 'a -> 'a) (ty : ty) (acc : 'a) : 'a =
  match ty with 
  | Message | Boolean | Index | Timestamp
  | TBase _ | TVar _ | TUnivar _ ->
    acc
    
  | Tuple l -> List.fold_left ((^~) f) acc l
                 
  | Fun (ty1, ty2) -> f ty1 (f ty2 acc) 

let map (f : ty -> ty) (ty : ty) : ty =
  match ty with 
  | Message | Boolean | Index | Timestamp
  | TBase _ | TVar _ | TUnivar _ ->
    ty
    
  | Tuple l -> Tuple (List.map f l)
                 
  | Fun (ty1, ty2) -> Fun (f ty1, f ty2)

let map_fold (f : ty -> 'a -> ty * 'a) (ty : ty) (acc : 'a) : ty * 'a =
  match ty with 
  | Message | Boolean | Index | Timestamp
  | TBase _ | TVar _ | TUnivar _ ->
    ty, acc
    
  | Tuple l ->
    let acc, l =
      List.fold_left_map
        (fun acc ty -> let acc, ty = f ty acc in ty, acc)
        acc l
    in
    Tuple l, acc
                 
  | Fun (ty1, ty2) ->
    let ty1, acc = f ty1 acc in
    let ty2, acc = f ty2 acc in
    Fun (ty1, ty2), acc

let iter (f : ty -> unit) (ty : ty) : unit =
  fold (fun ty () -> f ty) ty () 

let forall (f : ty -> bool) (ty : ty) : bool =
  fold (fun ty b -> b && f ty) ty true

let exists (f : ty -> bool) (ty : ty) : bool =
  fold (fun ty b -> b || f ty) ty false 

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
(** {2 Misc} *)

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
let toplevel_prec = 0

let fun_fixity   = 10, `Infix `Right
let tuple_fixity = 20, `NonAssoc

let _pp ~dbg : Format.formatter -> ty -> unit = 
  let rec _pp 
      ((outer,side) : ('b * fixity) * assoc)
      (ppf : Format.formatter) (t : ty) : unit 
    = 
    match t with
    | Message   -> Fmt.pf ppf "message"
    | Index     -> Fmt.pf ppf "index"
    | Timestamp -> Fmt.pf ppf "timestamp"
    | Boolean   -> Fmt.pf ppf "bool"
    | TBase s   -> Fmt.pf ppf "%s" s
    | TVar id   -> _pp_tvar ~dbg ppf id
    | TUnivar u -> pp_univar ppf u

    | Tuple tys -> 
      let pp ppf () =
        Fmt.list ~sep:(Fmt.any " * ") (_pp (tuple_fixity,`Left)) ppf tys
      in
      maybe_paren ~outer ~side ~inner:tuple_fixity pp ppf ()

    | Fun (t1,t2) -> 
      let pp ppf () =
        Fmt.pf ppf "@[<0>%a ->@ %a@]"
          (_pp (fun_fixity, `Left )) t1
          (_pp (fun_fixity, `Right)) t2
      in
      maybe_paren ~outer ~side ~inner:fun_fixity pp ppf ()
  in
  _pp ((toplevel_prec, `NoParens), `NonAssoc) 

let pp     = _pp ~dbg:false
let pp_dbg = _pp ~dbg:true

(** Encoding of a type as a string without discontinuity nor
    parenthesis. *)
let to_string (ty : ty) : string =
  let rec doit ppf = function
    | Message   -> Fmt.pf ppf "message"
    | Index     -> Fmt.pf ppf "index"
    | Timestamp -> Fmt.pf ppf "timestamp"
    | Boolean   -> Fmt.pf ppf "bool"
    | TBase s   -> Fmt.pf ppf "%s" s
    | TVar id   -> pp_tvar ppf id
    | TUnivar u -> pp_univar ppf u

    | Tuple tys -> Fmt.list ~sep:(Fmt.any "•") pp ppf tys

    | Fun (t1, t2) ->
      Fmt.pf ppf "%a→%a" doit_chain_left t1 pp t2
        
  and doit_chain_left ppf (t : ty) : unit =
    match t with
    | Fun (_, _) -> Fmt.pf ppf "_%a_" pp t
    | _          -> Fmt.pf ppf "%a"   pp t
  in
  Fmt.str "%a" doit ty
  
(*------------------------------------------------------------------*)
let rec contains_tuni = function
  | TUnivar _ -> true
  | _ as ty -> exists contains_tuni ty

let rec is_bitstring_encodable = function 
  | Message
  | Boolean
  | Index  
  | Timestamp
  | TBase _  -> true

  | Tuple tys -> List.for_all is_bitstring_encodable tys

  | Fun _ | TVar _ | TUnivar _ -> false

(*------------------------------------------------------------------*)
let fv (t : ty) : Fv.t = 
  let rec fuvs acc t =
    match t with
    | Message
    | Boolean
    | Index  
    | Timestamp
    | TBase _  -> acc
      
    | TUnivar ui -> Fv.add_uv ui acc
    | TVar    ti -> Fv.add_tv ti acc

    | Tuple tys -> List.fold_left fuvs acc tys
    | Fun (t1, t2) -> fuvs (fuvs acc t1) t2
  in
  fuvs Fv.empty t
               
let fvs l =
  List.fold_left (fun uvs v -> Fv.union uvs (fv v)) Fv.empty l

(*------------------------------------------------------------------*)
(** {2 Type substitution } *)
              
(** A type substitution*)
type tsubst = {
  ts_univar : ty Ident.Mid.t;
  ts_tvar   : ty Ident.Mid.t;
}

let pp_tsubst fmt ts =
  let pp_bd fmt (id,ty) = 
    Fmt.pf fmt "@[%a → %a@]" Ident.pp_full id pp ty
  in
  Fmt.pf fmt "@[<v 0>@[<hov 2>univars:@ %a@]@;@[<hov 2>tvars:@ %a@]@]" 
    (Fmt.list ~sep:Fmt.comma pp_bd) (Mid.bindings ts.ts_univar)
    (Fmt.list ~sep:Fmt.comma pp_bd) (Mid.bindings ts.ts_tvar)


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

  val copy : env -> env
  val set : tgt:env -> value:env -> unit
    
  val mk_univar : env -> univar

  val open_tvars : env -> tvars -> univars * tsubst

  val norm   : env -> ty  -> ty
                         
  val unify_eq  : env -> ty -> ty -> [`Fail | `Ok]

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
            Fmt.pf fmt "@[<hv 2>@[%a@] →@ @[%a@]@]" Ident.pp_full id pp ty
      )) (Mid.bindings !e)

  let mk_env () = ref Mid.empty 

  let copy env = ref (!env) 

  let set ~tgt ~value = tgt := !value

  let mk_univar (env : env) =
    let uv = Ident.create "_u" in
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

  (** An type inference environment [ty_env] is closed if every unification 
      variable normal form is a type that do not use univars in [ty_env]
      (but may use other univars). *)
  let is_closed (env : env) : bool =
    let rec check = function
      | TUnivar uv -> not (Mid.mem uv !env)
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
end


(*------------------------------------------------------------------*)
(** {2 Type destructors and constructors} *)

(** Exception not exported *)
exception DestrFailed

let rec destr_funs ?ty_env (t : ty) (i : int) : ty list * ty =
  match t, i with
  | _, 0 -> [], t

  | Fun (t1, t2), _ -> 
    let lty, tout = destr_funs t2 (i - 1) in
    t1 :: lty, tout

  | TUnivar _, _ when ty_env <> None -> 
    let ty_env = oget ty_env in

    let ty_args = List.init i (fun _ -> TUnivar (Infer.mk_univar ty_env)) in
    let ty_out = TUnivar (Infer.mk_univar ty_env) in
    let () =
      match Infer.unify_eq ty_env t (fun_l ty_args ty_out) with
      | `Fail -> raise DestrFailed
      | `Ok   -> ()
    in

    ty_args, ty_out

  | _ -> raise DestrFailed

let destr_funs_opt ?ty_env t i =  
  try Some (destr_funs ?ty_env t i) with DestrFailed -> None

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
  let pp_ty fmt =
    Fmt.pf fmt "%a" pp (fun_l fty.fty_args fty.fty_out)
  in
  if fty.fty_vars = [] then
    Fmt.pf fmt "@[<hov 2>%t@]"
      pp_ty
  else
    Fmt.pf fmt "@[<hov 2>[%a] %t@]"
      (Fmt.list ~sep:Fmt.comma pp_g) fty.fty_vars
      pp_ty
    
let pp_ftype    = pp_ftype_g pp_univar
let pp_ftype_op = pp_ftype_g pp_tvar

(*------------------------------------------------------------------*)
let ftype_fv (f : ftype) : Fv.t =
  (* [f.fty_vars] are not free in [f], and must not be added. *)
  Fv.rem_tvs
    f.fty_vars
    (Fv.union
       (fvs f.fty_args)
       (fv f.fty_out)) 

(*------------------------------------------------------------------*)
let tsubst_ftype (ts : tsubst) (fty : ftype) : ftype = { 
  fty_vars = fty.fty_vars;              (* bound type variable *)
  fty_args = List.map (tsubst ts) fty.fty_args;
  fty_out  = tsubst ts fty.fty_out;
  }
    
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
(** {2 Freshen function types} *)

let open_ftype (ty_env : Infer.env) (fty : ftype) : ftype_op =
  let vars_f, ts = Infer.open_tvars ty_env fty.fty_vars in

  (* compute the new function type *)
  { fty_vars = vars_f;
    fty_args = List.map (tsubst ts) fty.fty_args;
    fty_out  = tsubst ts fty.fty_out; }
  
