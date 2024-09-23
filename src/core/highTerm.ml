module SE = SystemExpr

(*------------------------------------------------------------------*)
include Term

module Smart : SmartFO.S with type form = Term.term = struct
  type form = Term.t

  include Term.Smart

  let[@warning "-27"] destr_exists_tagged  ~env x = destr_exists_tagged  x
  let[@warning "-27"] destr_exists         ~env x = destr_exists         x
  let[@warning "-27"] destr_exists1_tagged ~env x = destr_exists1_tagged x
  let[@warning "-27"] destr_exists1        ~env x = destr_exists1        x
  let[@warning "-27"] destr_or             ~env x = destr_or             x
  let[@warning "-27"] destr_impl           ~env x = destr_impl           x
  let[@warning "-27"] destr_impls          ~env x = destr_impls          x
  let[@warning "-27"] destr_ors            ~env x = destr_ors            x
  let[@warning "-27"] is_or                ~env x = is_or                x
  let[@warning "-27"] is_impl              ~env x = is_impl              x
  let[@warning "-27"] is_exists            ~env x = is_exists            x
  let[@warning "-27"] decompose_ors        ~env x = decompose_ors        x
  let[@warning "-27"] decompose_impls      ~env x = decompose_impls      x
  let[@warning "-27"] decompose_impls_last ~env x = decompose_impls_last x
end

(*------------------------------------------------------------------*)
type tags = {
  const : bool;
  adv   : bool;
  si    : bool;
  det   : bool;
}

let mk_tags
  ?(const = false)
  ?(adv   = false)
  ?(si    = false)
  ?(det   = false)
  ()
  =
  { const ; adv ; si ; det }

let to_vars_tags (tags : tags) : Vars.Tag.t =
  { const        = tags.const ;
    adv          = tags.adv ;
    system_indep = tags.si }

let merge_tags (tags1 : tags) (tags2 : tags): tags =
  {
    const = tags1.const && tags2.const ;
    adv   = tags1.adv   && tags2.adv   ;
    si    = tags1.si    && tags2.si    ;
    det   = tags1.det   && tags2.det   ;
  }
    
(*------------------------------------------------------------------*)
let tags_of_term (env : Env.t) ~ty_env (t : Term.term) : tags =

  let rec doit_subterms (env : Env.t) (t : Term.term) : tags =
    Term.tfold
      (fun term tag -> merge_tags tag (doit env term))
      t { const = true; adv = true; si = true; det = true }

  and doit (env : Env.t) (t : Term.term) : tags =
    match t with
    | Var v ->
      let info = try Vars.get_info v env.vars with Not_found -> Vars.Tag.gtag in
      let ty_v = Type.Infer.norm ty_env (Vars.ty v) in
      let is_ty_enum = Symbols.TyInfo.is_enum env.table ty_v in
      let is_ty_encodable = Type.is_bitstring_encodable ty_v in
      let adv =
        (* FIXME: could be improved into `info.det && is_ty_enum` *)
        (info.const && is_ty_enum) || 
        (info.const && is_ty_encodable) ||
        info.adv
      in
      {
        const = info.const        ;
        adv   = adv               ;
        si    = info.system_indep ;
        det   = info.const        ;
      }

    | Name _ ->
      let merged = doit_subterms env t in
      mk_tags ~si:merged.si ()

    | Macro _ -> mk_tags ()

    | Fun (f,_) -> 
      let is_att = f = Symbols.fs_att || f = Symbols.fs_qatt in
      let is_si = Operator.is_system_indep env.table f in
      {
        const = not is_att ;
        adv   = true       ;
        si    = is_si      ;
        det   = not is_att ;
      }

    | Find (vs, _, _, _) | Quant (_,vs,_) ->
      let vs_tys = List.map (fun v -> Type.Infer.norm ty_env (Vars.ty v)) vs in
      let fixed_type_binders =
        List.for_all (Symbols.TyInfo.is_fixed env.table) vs_tys
      in
      let poly_card_type_binders =
        List.for_all (fun ty ->
            Symbols.TyInfo.is_fixed  env.table ty &&
            Symbols.TyInfo.is_finite env.table ty
          ) vs_tys
      in
      let is_lambda = match t with Quant (Lambda,_,_) -> true | _ -> false in
      let merged =
        let vars = Vars.Tag.global_vars ~const:true ~adv:true vs in
        let venv = Vars.add_vars vars env.vars in
        let env = Env.update ~vars:venv env in
        doit_subterms env t 
      in
      let adv =
        if poly_card_type_binders || is_lambda then merged.adv else false
      in
      let const, si, det =
        merged.const && fixed_type_binders, merged.si, merged.det
      in
      { const; adv; si; det }

    | App _| Action _ | Tuple _ | Proj _ ->
      doit_subterms env t

    | Diff _ ->
      let merged = doit_subterms env t in
      { merged with si = false }

    | Let (v,t1,t2) ->
      let tags = to_vars_tags (doit env t1) in
      let venv = Vars.add_vars [v, tags] env.vars in
      let env = Env.update ~vars:venv env in
      doit env t2
  in
  let tags = doit env t in
  { tags with
    si =
      (* a term is system-independent if it applies to a single system
         (for both set and pair), or if it uses only system-independent
         constructs *)
      SE.is_single_system env.system || tags.si; }
  
(*------------------------------------------------------------------*)
let is_system_indep
    ?(ty_env:Type.Infer.env = Type.Infer.mk_env ())
    (env : Env.t) (t : Term.term)
  : bool
  =
  (tags_of_term ~ty_env env t).si

let is_deterministic
    ?(ty_env:Type.Infer.env = Type.Infer.mk_env ())
    (env : Env.t) (t : Term.term)
  : bool
  =
  (tags_of_term ~ty_env env t).det

let is_constant
    ?(ty_env:Type.Infer.env = Type.Infer.mk_env ())
    (env : Env.t) (t : Term.term) : bool
  =
  (tags_of_term env ~ty_env t).const

let is_ptime_deducible
    ~(si : bool)
    ?(ty_env:Type.Infer.env = Type.Infer.mk_env ())
    (env : Env.t) (t : Term.term) : bool
  =
  let tags = tags_of_term env ~ty_env t in
  tags.adv && (not si || tags.si) 

(*------------------------------------------------------------------*)
(** Exported, shadows the previous definition. *)
let tags_of_term
    ?(ty_env : Type.Infer.env = Type.Infer.mk_env ())
    (env : Env.t) (t : Term.term)
  : Vars.Tag.t
  =
  let tags = tags_of_term ~ty_env env t in
  {
    system_indep = tags.si    ;
    const        = tags.const ;
    adv          = tags.adv   ;
  }
