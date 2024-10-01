open Utils

(*------------------------------------------------------------------*)
module Mid = Ident.Mid

(* an unification environment *)
type env = Type.ty Mid.t ref

let pp fmt (e : env) =
  Fmt.pf fmt "[@[<v 0>%a@]]"
    (Fmt.list ~sep:Fmt.cut
       (fun fmt (id, ty) ->
          Fmt.pf fmt "@[<hv 2>@[%a@] →@ @[%a@]@]" Ident.pp_full id Type.pp ty
       )) (Mid.bindings !e)

let mk_env () = ref Mid.empty 

let copy env = ref (!env) 

let set ~tgt ~value = tgt := !value

(*------------------------------------------------------------------*)
let mk_ty_univar (env : env) : Type.univar =
  let uv = Ident.create "_u" in
  let ety = Type.univar uv in
  env := Mid.add uv ety !env;
  uv

let open_tvars ty_env (tvars : Type.tvars) =
  let vars_f = List.map (fun _ -> mk_ty_univar ty_env) tvars in

  (* create substitution refreshing all type variables *)
  let ts_tvar =
    List.fold_left2 (fun ts_tvar (id : Type.tvar) id_f ->        
        Mid.add (id :> Ident.t) (Type.univar id_f) ts_tvar
      ) Mid.empty tvars vars_f
  in  
  let ts = Type.mk_tsubst ~univars:Mid.empty ~tvars:ts_tvar in
  vars_f, ts

(* Univar are maximal for this ordering *)
let compare (t : Type.ty) (t' : Type.ty) : int =
  match t, t' with
  | TUnivar u, TUnivar u' -> Ident.compare u u'
  | TUnivar _, _ -> 1
  | _, TUnivar _ -> -1
  | _, _ -> Stdlib.compare t t'

let rec norm (env : env) (t : Type.ty) : Type.ty =
  match t with
  | TUnivar u ->
    let u' = Mid.find_dflt t u !env in
    if t = u' then u' else norm env u'

  | Fun (t1, t2) -> Type.func (norm env t1) (norm env t2)

  | Tuple l -> Type.tuple (List.map (norm env) l)

  | Message | Boolean | Index | Timestamp | TBase _ | TVar _ -> t

let norm_ty = norm

let norm_env (env : env) : unit = 
  env := Mid.map (norm env) !env

(** An type inference environment [ty_env] is closed if every unification 
    variable normal form is a type that do not use univars in [ty_env]
    (but may use other univars). *)
let is_closed (env : env) : bool =
  let rec check : Type.ty -> bool = function
    | TUnivar uv -> not (Mid.mem uv !env)
    | Message | Boolean | Index | Timestamp | TBase _ | TVar _ -> true
    | Fun (t1, t2) -> check t1 && check t2
    | Tuple l -> List.for_all check l
  in

  norm_env env;
  Mid.for_all (fun _ -> check) !env

let close (env : env) : Type.tsubst =
  assert (is_closed env);
  Type.mk_tsubst ~tvars:Mid.empty ~univars:!env

(** Generalize unification variables and close the unienv. *)
let gen_and_close (env : env) : Type.tvars * Type.tsubst =
  (* find all univar that are unconstrained and generalize them.
     Compute: 
     - generalized tvars, 
     - substitution from univar to generalized tvars *)
  let rec gen0 (gen_tvars, ts_univar) (ty : Type.ty) =
    match ty with
    | TUnivar uid ->
      let tv = Ident.fresh uid in
      ( tv :: gen_tvars, 
        Mid.add uid (Type.tvar tv) ts_univar )

    | Tuple l -> List.fold_left gen0 (gen_tvars, ts_univar) l

    | Fun (t1, t2) -> gen0 (gen0 (gen_tvars, ts_univar) t1) t2

    | TVar _ | TBase _
    | Message | Boolean | Timestamp | Index ->
      gen_tvars, ts_univar
  in
  let gen acc ty = gen0 acc (norm env ty) in

  let gen_tvars, univars = 
    Mid.fold (fun _ ty acc -> gen acc ty) !env ([], Mid.empty)
  in
  let ts = Type.mk_tsubst ~univars ~tvars:Mid.empty in
  env := Mid.map (Type.tsubst ts) !env;

  (* close the resulting environment *)
  gen_tvars, close env

let unify_eq (env : env) (t : Type.ty) (t' : Type.ty) : [`Fail | `Ok] =
  let t  = norm env t
  and t' = norm env t' in

  let rec do_unif t t' : bool =
    let t, t' = if compare t t' < 0 then t', t else t, t' in

    if Type.equal t t'
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
