open Utils

(*------------------------------------------------------------------*)
module SE = SystemExprSyntax

module Mid = Ident.Mid
module Msv = SE.Var.M

(*------------------------------------------------------------------*)
(** A unification environment.

    Unification variables must be created through the [mk_ty_univar]
    and [mk_se_univar] functions below. *)
type env0 = {
  ty : Type.ty        Mid.t;      (** for type unification variables *)
  se : < > SE.exposed Msv.t;      (** for system variables *)
}

type env = env0 ref

(*------------------------------------------------------------------*)
let pp fmt (e : env) =
  Fmt.pf fmt "[@[<v 0>\
              @[<v 2>Types:@;%a@]@;\
              @[<v 2>System variables:@;%a@]]"

    (* types *)
    (Fmt.list ~sep:Fmt.cut
       (fun fmt (id, ty) ->
          Fmt.pf fmt "@[<hv 2>@[%a@] →@ @[%a@]@]" Ident.pp_full id Type.pp ty
       )) (Mid.bindings !e.ty)

    (* system expressions *)
    (Fmt.list ~sep:Fmt.cut
       (fun fmt (id, ty) ->
          Fmt.pf fmt "@[<hv 2>@[%a@] →@ @[%a@]@]" SE.Var.pp id SE.pp (SE.force ty)
       )) (Msv.bindings !e.se)

(*------------------------------------------------------------------*)
let mk_env () = ref { ty = Mid.empty; se = Msv.empty; }

let copy (env : env) : env = ref (!env) 

let set ~(tgt : env) ~(value : env) : unit =
  tgt := !value

(*------------------------------------------------------------------*)
let mk_ty_univar (env : env) : Type.univar =
  let uv = Ident.create "_u" in
  let ety = Type.univar uv in
  env := { !env with ty = Mid.add uv ety !env.ty; };
  uv

(*------------------------------------------------------------------*)
let mk_se_univar (env : env) : SE.Var.t =
  let uv = SE.Var.of_ident (Ident.create "_s") in 
  let e = SE.{ cnt = SE.Var uv; name = None; } in
  env := { !env with se = Msv.add uv e !env.se; };
  uv

(*------------------------------------------------------------------*)
let open_tvars (env : env) (tvars : Type.tvars) =
  let vars_f = List.map (fun _ -> mk_ty_univar env) tvars in

  (* create substitution refreshing all type variables *)
  let ts_tvar =
    List.fold_left2 (fun ts_tvar (id : Type.tvar) id_f ->        
        Mid.add (id :> Ident.t) (Type.univar id_f) ts_tvar
      ) Mid.empty tvars vars_f
  in  
  let ts = Subst.mk_subst ~univars:Mid.empty ~tvars:ts_tvar in
  vars_f, ts

(*------------------------------------------------------------------*)
(** [univar] are maximal for this ordering *)
let compare (t : Type.ty) (t' : Type.ty) : int =
  match t, t' with
  | TUnivar u, TUnivar u' -> Ident.compare u u'
  | TUnivar _, _ -> 1
  | _, TUnivar _ -> -1
  | _, _ -> Stdlib.compare t t'

let norm_ty (env : env) (t : Type.ty) : Type.ty =
  let rec doit : Type.ty -> Type.ty = function
    | TUnivar u as t ->
      let u' = Mid.find_dflt t u !env.ty in
      if Type.equal t u' then u' else doit u'

    | Fun (t1, t2) -> Type.func (doit t1) (doit t2)

    | Tuple l -> Type.tuple (List.map doit l)

    | Message | Boolean | Index | Timestamp | TBase _ | TVar _ as t -> t
  in
  doit t

let norm_se0 (env : env) (se : < > SE.exposed) : < > SE.exposed =
  let rec doit (se : < > SE.exposed) : < > SE.exposed = 
    match se.cnt with
    | Var v -> 
      let v' = Msv.find_dflt se v !env.se in
      if se = v' then v' else doit v'

    | Any _ | List _ -> se
  in
  doit se

let norm_se (type a) (env : env) (se : a SE.expr) : a SE.expr =
  SE.force (norm_se0 env (se :> < > SE.exposed))

(*------------------------------------------------------------------*)
let norm_env (env : env) : unit = 
  env := { 
    ty = Mid.map (norm_ty  env) !env.ty; 
    se = Msv.map (norm_se0 env) !env.se; 
  }

(*------------------------------------------------------------------*)
(** An type inference environment [env] is closed if every unification
    variable have a normal form that do not use univars in [env] (but
    may use other univars). *)
let is_closed (env : env) : bool =
  let rec check_ty : Type.ty -> bool = function
    | TUnivar uv -> not (Mid.mem uv !env.ty)
    | _ as ty -> Type.forall check_ty ty
  in

  let check_se (se : < > SE.exposed) : bool = 
    match se.cnt with
    | Var uv -> not (Msv.mem uv !env.se)
    | Any _ | List _ -> true 
  in

  norm_env env;

  Mid.for_all (fun _ -> check_ty) !env.ty &&
  Msv.for_all (fun _ -> check_se) !env.se

(*------------------------------------------------------------------*)
let close (env : env) : Subst.t =
  assert (is_closed env);
  Subst.mk_subst ~tvars:Mid.empty ~univars:!env.ty

(*------------------------------------------------------------------*)
(** Generalize unification variables and close the unienv. *)
let gen_and_close (env : env) : Type.tvars * Subst.t =
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
  let gen acc ty = gen0 acc (norm_ty env ty) in

  let gen_tvars, univars = 
    Mid.fold (fun _ ty acc -> gen acc ty) !env.ty ([], Mid.empty)
  in
  let ts = Subst.mk_subst ~univars ~tvars:Mid.empty in
  env := { !env with ty = Mid.map (Subst.subst_ty ts) !env.ty; };

  (* close the resulting environment *)
  gen_tvars, close env

let unify_eq (env : env) (t : Type.ty) (t' : Type.ty) : [`Fail | `Ok] =
  let t  = norm_ty env t
  and t' = norm_ty env t' in

  let rec do_unif t t' : bool =
    let t, t' = if compare t t' < 0 then t', t else t, t' in

    if Type.equal t t'
    then true
    else match t, t' with
      | TUnivar u, _ -> env := { !env with ty = Mid.add u t' !env.ty; }; true
      | Tuple tl, Tuple tl' ->
        List.length tl = List.length tl' &&
        do_unifs tl tl'

      | Fun (t1, t2), Fun (t1', t2') ->
        do_unifs [t1; t2] [t1'; t2']

      | _ -> false

  and do_unifs l l' = List.for_all2 do_unif l l' in

  if do_unif t t' then `Ok else `Fail
