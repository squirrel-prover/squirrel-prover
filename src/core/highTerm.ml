module SE = SystemExpr

(*------------------------------------------------------------------*)
include Term

module Smart : SmartFO.S with type form = Term.term = struct
  type form = Term.t

  include Term.Smart

  let[@warning "-27"] destr_exists_tagged  ?env x = destr_exists_tagged  x
  let[@warning "-27"] destr_exists         ?env x = destr_exists         x
  let[@warning "-27"] destr_exists1_tagged ?env x = destr_exists1_tagged x
  let[@warning "-27"] destr_exists1        ?env x = destr_exists1        x
  let[@warning "-27"] destr_or             ?env x = destr_or             x
  let[@warning "-27"] destr_impl           ?env x = destr_impl           x
  let[@warning "-27"] destr_ors            ?env x = destr_ors            x
  let[@warning "-27"] is_or                ?env x = is_or                x
  let[@warning "-27"] is_impl              ?env x = is_impl              x
  let[@warning "-27"] is_exists            ?env x = is_exists            x
end

(*------------------------------------------------------------------*)
type tags = {
  const : bool;
  adv   : bool;
  si    : bool;
  ptime : bool;
  det   : bool;
}

let mk_tags
  ?(const = false)
  ?(adv   = false)
  ?(si    = false)
  ?(ptime = false)
  ?(det   = false)
  ()
  =
  { const ; adv ; si ; ptime ; det }

let to_vars_tags (tags : tags) : Vars.Tag.t =
  { const        = tags.const ;
    adv          = tags.adv ;
    system_indep = tags.si }

type goal = AllTags | Adv | NotAdv

let merge_tags (merge : bool -> bool -> bool) (tags1 : tags) (tags2 : tags): tags =
  { const = merge tags1.const tags2.const ; 
    adv   = merge tags1.adv   tags2.adv   ; 
    si    = merge tags1.si    tags2.si    ; 
    ptime = merge tags1.ptime tags2.ptime ; 
    det   = merge tags1.det   tags2.det }

let and_tags_list : tags list -> tags =
  List.fold_left
    (merge_tags (&&))
    { const = true; adv = true; si = true; ptime = true; det = true }

let rec tag_of_term_full
    (goal : goal)
    (env : Env.t)
    ?(ty_env : Type.Infer.env = Type.Infer.mk_env ())
    (t : Term.term) : tags
  =
  (*TODO check link between ptime and si*)
  let get_subterms_tags goal env ~ty_env t : tags list =
    Term.tfold
      (fun term list -> tag_of_term_full goal env ~ty_env term :: list)
      t []
  in
  match t with 
  | Var v ->
    let info = Vars.get_info v env.vars in
    let ty_v = Type.Infer.norm ty_env (Vars.ty v) in
    let is_ty_fixed = Symbols.TyInfo.is_fixed env.table ty_v in
    let is_ty_finite = Symbols.TyInfo.is_finite env.table ty_v in
    let is_ty_encodable = Type.is_bitstring_encodable ty_v in
    let adv =
      (info.const && is_ty_finite && is_ty_fixed) ||
      (info.const && is_ty_encodable) ||
      info.adv
    in
    {
      const = info.const        ;
      adv   = adv               ;
      si    = info.system_indep ;
      ptime = adv               ;
      det   = info.const        ;
    }

  | Name _ -> 
    let st_tags = get_subterms_tags goal env ~ty_env t in
    let merged = and_tags_list st_tags in
    mk_tags ~si:merged.si ()
      
  | Macro _ -> mk_tags ()

  | Fun (f,_) -> (*TODO : Check carefully. I am not sure Term.tfold have no effect on Fun*)
    let is_att = f = Symbols.fs_att || f = Symbols.fs_qatt in
    let is_si = Operator.is_system_indep env.table f in
    {
      const = not is_att ;
      adv   = true       ;
      si    = is_si      ;
      ptime = true       ;
      det   = not is_att ;
    }
    
  | Find (vs, _, _, _) | Quant (_,vs,_) ->
    let fixed_type_binders =
      List.for_all (fun v -> 
          Symbols.TyInfo.is_fixed env.table (Type.Infer.norm ty_env (Vars.ty v))
        ) vs 
    in
    let poly_card_type_binders =
      List.for_all (fun v ->
          let ty_v = Type.Infer.norm ty_env (Vars.ty v) in
          Symbols.TyInfo.is_fixed  env.table ty_v &&
          Symbols.TyInfo.is_finite env.table ty_v 
        ) vs 
    in
    let adv, ptime =
      match goal with
      | AllTags | Adv ->
        if poly_card_type_binders then
          let vars = Vars.Tag.global_vars ~const:true ~adv:true vs in
          let venv = Vars.add_vars vars env.vars in
          let env = Env.update ~vars:venv env in
          let st_tags = get_subterms_tags Adv env ~ty_env t in
          let merged = and_tags_list st_tags in
          merged.adv, merged.ptime
        else
          false, false
      | NotAdv -> false, false
    in
    let const, si, det =
      match goal with
      | AllTags | NotAdv ->
        let vars = Vars.Tag.global_vars ~const:true vs in
        let venv = Vars.add_vars vars env.vars in
        let env = Env.update ~vars:venv env in
        let st_tags = get_subterms_tags NotAdv env ~ty_env t in
        let merged = and_tags_list st_tags in
        merged.const && fixed_type_binders, merged.si, merged.det
      | Adv -> false, false, false
    in
    { const; adv; si; ptime; det }
    
  | App _| Action _ | Tuple _ | Proj _ -> 
    let st_tags = get_subterms_tags goal env ~ty_env t in
    let merged = and_tags_list st_tags in
    merged
      
  | Diff _ -> 
    let st_tags = get_subterms_tags goal env ~ty_env t in
    let merged = and_tags_list st_tags in
    { merged with si = false }
    
  | Let (v,t1,t2) ->
    let tags = to_vars_tags (tag_of_term_full goal env ~ty_env t1) in
    let venv = Vars.add_vars [v, tags] env.vars in
    let env = Env.update ~vars:venv env in
    tag_of_term_full AllTags env ~ty_env t2

let is_system_indep (env : Env.t) (t : Term.term) : bool =
  (tag_of_term_full AllTags env t).si

let is_deterministic (env : Env.t) (t : Term.term) : bool =
  (tag_of_term_full AllTags env t).det

let is_constant
    ?(ty_env:Type.Infer.env = Type.Infer.mk_env ())
    (env : Env.t) (t : Term.term) : bool
  =
  (tag_of_term_full AllTags env ~ty_env t).const

let is_ptime_deducible
    ~(si : bool)
    ?(ty_env:Type.Infer.env = Type.Infer.mk_env ())
    (env : Env.t) (t : Term.term) : bool
  =
  let tags = tag_of_term_full AllTags env ~ty_env t in
  tags.ptime && (not si || tags.si) 

let tag_of_term (env : Env.t) (t : Term.term) : Vars.Tag.t =
  let tags = tag_of_term_full AllTags env t in
  {
    system_indep = tags.si    ;
    const        = tags.const ;
    adv          = tags.adv   ;
  }
