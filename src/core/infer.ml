open Utils

(*------------------------------------------------------------------*)
module SE = SystemExprSyntax

module Mid = Ident.Mid
module Sid = Ident.Sid
module Msv = SE.Var.M

(*------------------------------------------------------------------*)
(** A unification environment.

    Unification variables must be created through the [mk_ty_univar]
    and [mk_se_univar] functions below. *)
type env0 = {
  ty : Type.ty        Mid.t;
  (** for type unification variables *)

  se : (SE.exposed * SE.Var.info list) Msv.t;
  (** for system variables
      (we use the exposed type to be able to easily inspect the
      expressions) *)
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
       (fun fmt (id, (se,infos)) ->
          Fmt.pf fmt "@[<hv 2>@[%a@]%t →@ @[%a@]@]"
            SE.Var.pp id
            (fun fmt ->
               if infos = [] then () else
                 Fmt.pf fmt "@[[%a]@]" (Fmt.list SE.Var.pp_info) infos)
            SE.pp (SE.force se)
       )) (Msv.bindings !e.se)

(*------------------------------------------------------------------*)
let mk_env () = ref { ty = Mid.empty; se = Msv.empty; }

let copy (env : env) : env = ref (!env)

let set ~(tgt : env) ~(value : env) : unit =
  tgt := !value

(*------------------------------------------------------------------*)
let mk_ty_univar (env : env) : Type.univar =
  let uv = Ident.create "?u" in
  let ety = Type.univar uv in
  env := { !env with ty = Mid.add uv ety !env.ty; };
  uv

(*------------------------------------------------------------------*)
let mk_se_univar
    ?(constraints:SE.Var.info list = []) (env : env)
  : SE.Var.t
  =
  let uv = SE.Var.of_ident (Ident.create "?P") in
  let e = SE.{ cnt = SE.Var uv; name = None; } in
  env := { !env with se = Msv.add uv (e,constraints) !env.se; };
  uv

(*------------------------------------------------------------------*)
let open_tvars ?(subst = Subst.empty_subst) (env : env) (tvars : Type.tvars) =
  let vars_f = List.map (fun _ -> mk_ty_univar env) tvars in

  (* create substitution refreshing all type variables *)
  let subst =
    List.fold_left2 (fun subst (id : Type.tvar) id_f ->
        Subst.add_tvar subst (id :> Ident.t) (Type.univar id_f) 
      ) subst tvars vars_f
  in
  vars_f, subst

(*------------------------------------------------------------------*)
let open_svars ?(subst = Subst.empty_subst) (env : env) (svars : SE.tagged_vars) =
  let vars_f = 
    List.map (fun (_,constraints) -> mk_se_univar ~constraints env) svars 
  in

  (* create substitution refreshing all type variables *)
  let subst =
    List.fold_left2 (fun subst ( (id,_) : _) id_f ->
        Subst.add_se_var subst id (SE.var id_f) 
      ) subst svars vars_f
  in
  vars_f, subst

(*------------------------------------------------------------------*)
let open_params (env : env) (p : Params.t) =
  let subst = Subst.empty_subst in
  let ty_vars, subst = open_tvars ~subst env p.ty_vars in
  let se_vars, subst = open_svars ~subst env p.se_vars in

  Params.Open.{ ty_vars; se_vars; }, subst

(*------------------------------------------------------------------*)
(** Internal exception *)
exception Cycle

(** When [fail_on_cycles] is [false], do not fail but return the type
    partially normalized.

    This is currently used in several exported functions, which use
    [norm_ty] to clean-up the types (e.g. before printing some
    user-level error). *)
let norm_ty ?(fail_on_cycles = true) (env : env) (t : Type.ty) : Type.ty =
  let rec doit (seen : Sid.t) : Type.ty -> Type.ty = function
    | TUnivar u as t ->
      if Sid.mem u seen then 
        if fail_on_cycles then raise Cycle else t
      else
        let u' = Mid.find_dflt t u !env.ty in
        if Type.equal t u' then u' else doit (Sid.add u seen) u'

    | Fun (t1, t2) -> Type.func (doit seen t1) (doit seen t2)

    | Tuple l -> Type.tuple (List.map (doit seen) l)

    | Message | Boolean | Index | Timestamp | TBase _ | TVar _ as t -> t
  in
  doit Sid.empty t

let norm_se0 (env : env) (se : SE.exposed) : SE.exposed =
  let rec doit (se : SE.exposed) : SE.exposed =
    match se.cnt with
    | Var v ->
      let v', _ = Msv.find_dflt (se,[]) v !env.se in
      if se = v' then v' else doit v'

    | Any | List _ -> se
  in
  doit se

let norm_se (type a) (env : env) (se : a SE.expr) : a SE.expr =
  SE.force (norm_se0 env (se :> SE.exposed))

let norm_se_context (env : env) (c : SE.context) : SE.context =
  { set = norm_se env c.set; pair = omap (norm_se env) c.pair; }

(** Exported *)
let norm_var (env : env) (v : Vars.var) = Vars.mk v.id (norm_ty ~fail_on_cycles:false env v.ty)

(*------------------------------------------------------------------*)
let norm_env (env : env) : [`Ok | `Cycle] =
  try
    env := {
      ty = Mid.map (norm_ty env)             !env.ty;
      se = Msv.map (fst_bind (norm_se0 env)) !env.se;
    };
    `Ok
  with Cycle -> `Cycle

(*------------------------------------------------------------------*)
(** Exported, see `.mli`. *)
let check_se_subst
    (env : Env.t)
    (v : SE.Var.t) (se : SE.t) (se_infos : SE.Var.info list)
  :
    [`Ok | `BadInst of Format.formatter -> unit]
  =
  let error (se_infos : SE.Var.info list) =
    `BadInst
      (fun fmt ->
         Fmt.pf fmt "@[<v 0>\
                     @[<hv 2>system variable substitution:@ \
                     @[%a → %a@]@]\
                     @;\
                     @[<hv 2>does not satisfy the system restriction%s:@ @[%a@]@]\
                     @]"
           SE.Var.pp v SE.pp se
           (if List.length se_infos = 1 then "" else "s")
           (Fmt.list ~sep:(Fmt.any "@, ") SE.Var.pp_info) se_infos)
  in
  let satisfies (se_info : SE.Var.info) =
    match se_info with
    | SE.Var.Pair ->
      begin
        match (se :> SE.exposed).cnt with
        | List l -> List.length l = 2
        | Var  v -> 
          let infos = List.assoc_dflt [] v env.se_vars in
          List.mem SE.Var.Pair infos
        | Any    -> false
      end

    | SE.Var.Compatible_with p -> 
      begin
        match SE.get_compatible_system env.se_vars se with
        | None -> false
        | Some p0 -> SystemSyntax.compatible env.table p0 p
      end
  in
  match List.filter (not -| satisfies) se_infos with
  | [] -> `Ok
  | l  -> error l

(*------------------------------------------------------------------*)
type 'a result =
  | Cycle
  | FreeTyVars
  | FreeSystemVars
  | BadInstantiation of (Format.formatter -> unit)
  | Closed of 'a

let pp_error_result fmt = function
  | Closed _           -> assert false
  | Cycle              -> Fmt.pf fmt "cycle in type inferrence"
  | FreeTyVars         -> Fmt.pf fmt "free type variables remaining"
  | FreeSystemVars     -> Fmt.pf fmt "free system variables remaining"
  | BadInstantiation e -> Fmt.pf fmt "bad system variable instantiation:@;%t" e

(*------------------------------------------------------------------*)
(** Return the substitution associated to an inference environment.

    Does **not** check that the environment is closed, nor that the
    substitution is valid (e.g. this function does not verify that the
    system expressions satisfy the required constraints). *)
let unsafe_to_subst (ienv : env) : Subst.t =
  let se_vars = Msv.map (SE.force -| fst) !ienv.se in
  Subst.mk_subst ~univars:!ienv.ty ~se_vars ()
  
(*------------------------------------------------------------------*)
let close (env : Env.t) (ienv : env) : Subst.t result =
  (* check that type unification variables have all been inferred *)
  let rec check_ty : Type.ty -> bool = function
    | TUnivar uv -> not (Mid.mem uv !ienv.ty)
    | _ as ty -> Type.forall check_ty ty
  in

  (* check that system expression variables have all been inferred *)
  let check_se (se : SE.exposed) : bool =
    match se.cnt with
    | Var uv -> not (Msv.mem uv !ienv.se)
    | Any | List _ -> true
  in

  (* check the instantiation of system variables *)
  let bad_se_instantiation =
    Msv.filter_map (fun v (se,infos) ->
        match check_se_subst env v (SE.force se) infos with
        | `Ok -> None
        | `BadInst err -> Some err
      ) !ienv.se
  in
  
  (* normalize the environment (by side-effects) + detect cycles *)
  if norm_env ienv <> `Ok then
    Cycle

  else if not (Mid.for_all (fun _ -> check_ty) !ienv.ty) then
    FreeTyVars

  else if not (Msv.for_all (fun _ (se,_) -> check_se se) !ienv.se) then
    FreeSystemVars

  else if not (Msv.is_empty bad_se_instantiation) then
    BadInstantiation (fun fmt ->
        Fmt.pf fmt "@[<v 0>%a@]"
          (Fmt.list
             ~sep:(Fmt.any "@;@;")
             (fun fmt (_,err) -> err fmt)
          ) (Msv.bindings bad_se_instantiation)
      )
  else Closed (unsafe_to_subst ienv)  (* safe call to [unsafe_to_subst] *)
      
(*------------------------------------------------------------------*)
(** Generalize unification variables and close the inference
    environment.
    Must be called on a normalized environment. *)     
let gen_and_close0
    (env : Env.t) (ienv : env) : (Params.t * Subst.t) result
  =
  (*------------------------------------------------------------------*)
  (* Find all type univars that are unconstrained and generalize them.
     Compute:
     - generalized tvars,
     - substitution from univar to generalized tvars *)

  let seen_univars = Hashtbl.create 16 in

  let rec gen_ty_univars0 (ty : Type.ty) (gen_tvars, subst) =
    match ty with
    | TUnivar uid when not (Hashtbl.mem seen_univars uid) ->
      Hashtbl.add seen_univars uid ();
      let tv = Ident.fresh uid in
      ( tv :: gen_tvars,
        Subst.add_univar subst uid (Type.tvar tv))

    | _ -> Type.fold gen_ty_univars0 ty (gen_tvars, subst)
  in
  let gen_ty_univars acc ty =
    gen_ty_univars0 ty acc
  in

  let gen_tvars, subst =
    Mid.fold
      (fun _ ty acc -> gen_ty_univars acc ty)
      !ienv.ty
      ([], Subst.empty_subst)
  in

  ienv := {
    !ienv with
    ty = Mid.map (Subst.subst_ty subst) !ienv.ty;
  };

  (*------------------------------------------------------------------*)
  (* For system expression variables, we look for variables appearing
     in normalized expressions and compute the accumulated set of
     constraints they must satisfy.

     Simultaneously, we check that inferred variables have been correctly
     instantiated.

     Return: (variables to generalize, failed variable instantiations)

     The latter is in reverse order. *)
  let check_and_gen_se_vars
      (v : SE.Var.t) ((se,infos) : SE.exposed * SE.Var.info list)
      (gen_se_vars, failed : SE.tagged_vars * (Format.formatter -> unit) list)
    :
      SE.tagged_vars * (Format.formatter -> unit) list
    =
    match se.cnt with
    | SE.Var v when Msv.exists (fun v' _ -> SE.Var.equal v v') !ienv.se ->
      (* If [v] is already in [gen_se_vars], we add [infos] to the
         constraints [v] must satisfy.
         Otherwise, we add [v,infos] to [gen_se_vars]. *)
      let gen_se_vars =
        List.assoc_up_dflt
          v infos
          (fun infos' -> List.sort_uniq Stdlib.compare (infos' @ infos) )
          gen_se_vars
      in
      (gen_se_vars, failed)

    | _ ->
      let failed =
        match check_se_subst env v (SE.force se) infos with
        | `Ok -> failed
        | `BadInst err -> err :: failed
      in
      (gen_se_vars, failed)
  in

  let gen_se_vars, failed =
    Msv.fold (fun v se acc -> check_and_gen_se_vars v se acc) !ienv.se ([], [])
  in
  let failed = List.rev failed in (* put [failed] in the correct order *)

  (* close the resulting environment *)
  match failed with
  | [] -> 
    let params = Params.{ ty_vars = gen_tvars; se_vars = gen_se_vars; } in
    Closed (params, unsafe_to_subst ienv) (* safe call to [unsafe_to_subst] *)

  | _  ->
    BadInstantiation
      (fun fmt ->
         Fmt.pf fmt "@[<v 0>%a@]"
           (Fmt.list ~sep:(Fmt.any "@;@;") (fun fmt -> Fmt.pf fmt "%t"))
           failed)

(*------------------------------------------------------------------*)
(** normalize [ienv] then call [gen_and_close0] *)
let gen_and_close (env : Env.t) (ienv : env) =
  (* normalize the environment (by side-effects) + detect cycles *)
  if norm_env ienv <> `Ok then
    Cycle
  else gen_and_close0 env ienv

(*------------------------------------------------------------------*)
(** [univar] are maximal for this ordering *)
(* FIXME: why don't we restrict ourselves to [univar] in the domain of
   the inference environment? (as in [compare_se] below) *)
let compare_ty (t : Type.ty) (t' : Type.ty) : int =
  match t, t' with
  | TUnivar u, TUnivar u' -> Ident.compare u u'
  | TUnivar _, _ -> 1
  | _, TUnivar _ -> -1
  | _, _ -> Stdlib.compare t t'

(*------------------------------------------------------------------*)
let unify_ty (env : env) (t : Type.ty) (t' : Type.ty) : [`Fail | `Ok] =
  let rec do_unif t t' : bool =
    let t, t' = if compare_ty t t' < 0 then t', t else t, t' in

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

  try
    let t  = norm_ty env t
    and t' = norm_ty env t' in
    if do_unif t t' then `Ok else `Fail
  with Cycle -> `Fail

(*------------------------------------------------------------------*)
(** system unification variables (i.e. variable in the domain of
    [!env.se] are maximal for this ordering *)
let compare_se (env : env) (t : SE.exposed) (t' : SE.exposed) : int =
  match t.cnt, t'.cnt with
  | Var u, Var u' when Msv.mem u !env.se && Msv.mem u' !env.se -> 
    Ident.compare (SE.Var.to_ident u) (SE.Var.to_ident u')
  | Var u, _ when Msv.mem u !env.se -> 1
  | _, Var u when Msv.mem u !env.se -> -1
  | _, _ -> Stdlib.compare t t'

(*------------------------------------------------------------------*)
let unify_se (env : env) (t : SE.t) (t' : SE.t) : [`Fail | `Ok] =
  let t  = (norm_se env t  :> SE.exposed)
  and t' = (norm_se env t' :> SE.exposed) in

  let t, t' = if compare_se env t t' < 0 then t', t else t, t' in

  if SE.equal0 (SE.force t) (SE.force t') then `Ok else
    match t.cnt, t'.cnt with
    | Var u, _ when Msv.mem u !env.se -> 
      (* [u] is a system unification variable. *)
      let _, infos = Msv.find u !env.se in
      env := { !env with se = Msv.add u (t',infos) !env.se; }; `Ok

    | _ -> `Fail

(*------------------------------------------------------------------*)
let unify_se_context
    (env : env) (c : SE.context) (c' : SE.context) 
  :
    [`Fail | `Ok] 
  =
  match unify_se env c.set c'.set with
  | `Fail -> `Fail
  | `Ok ->
    match c.pair, c'.pair with
    | Some p, Some p' -> unify_se env (p :> SE.t) (p' :> SE.t)
    | None, None -> `Ok
    | _ -> `Fail

(*------------------------------------------------------------------*)
(** Exported version of [norm_ty], with [fail_on_cycles] set to [false]. *)
let norm_ty = norm_ty ~fail_on_cycles:false
