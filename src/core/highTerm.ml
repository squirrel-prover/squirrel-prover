open Utils

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
  let[@warning "-27"] destr_and      ~mode ~env x = destr_and            x
  let[@warning "-27"] destr_ands     ~mode ~env x = destr_ands           x
      
  let[@warning "-27"] is_or                ~env x = is_or                x
  let[@warning "-27"] is_impl              ~env x = is_impl              x
  let[@warning "-27"] is_exists            ~env x = is_exists            x
  let[@warning "-27"] is_and         ~mode ~env x = is_and               x
      
  let[@warning "-27"] decompose_ors        ~env x = decompose_ors        x
  let[@warning "-27"] decompose_impls      ~env x = decompose_impls      x
  let[@warning "-27"] decompose_impls_last ~env x = decompose_impls_last x
  let[@warning "-27"] decompose_ands ~mode ~env x = decompose_ands       x
end

(*------------------------------------------------------------------*)
(** Tags that can be associated to a term [t] *)
type tags = {
  const   : bool;
  (** [t] is constant *)

  adv     : bool;
  (** [t] is computable in ptime by an adversary with no direct access
      to the protocol randomness *)

  si      : bool; 
  (** [t] system-independent, i.e. its semantics does not change when
      the system does *)

  no_diff : bool;
  (** [t] does no contain any diff (thus [t] could be seen as a single
      system) *)

  det     : bool;
  (** [t] is deterministic *)
}

let mk_tags
  ?(const   = false)
  ?(adv     = false)
  ?(si      = false)
  ?(det     = false)
  ?(no_diff = false)
  ()
  =
  { const ; adv ; si ; det; no_diff; }

let to_vars_tags (tags : tags) : Vars.Tag.t =
  { const        = tags.const ;
    adv          = tags.adv ;
    system_indep = tags.si }

let merge_tags (tags1 : tags) (tags2 : tags): tags =
  {
    const   = tags1.const   && tags2.const   ;
    adv     = tags1.adv     && tags2.adv     ;
    si      = tags1.si      && tags2.si      ;
    det     = tags1.det     && tags2.det     ;
    no_diff = tags1.no_diff && tags2.no_diff ;
  }
    
(*------------------------------------------------------------------*)
let tags_of_term (env : Env.t) ~ienv (t : Term.term) : tags =

  let rec doit_subterms (env : Env.t) (t : Term.term) : tags =
    Term.tfold
      (fun term tag -> merge_tags tag (doit env term))
      t { const = true; adv = true; si = true; det = true; no_diff = true; }

  and doit (env : Env.t) (t : Term.term) : tags =
    match t with
    | Int _ | String _ ->
      {
        const   = true ;
        adv     = true ;
        si      = true ;
        no_diff = true ;
        det     = true ;
      }

    | Var v ->
      let info = try Vars.get_info v env.vars with Not_found -> Vars.Tag.gtag in
      let ty_v = Infer.norm_ty ienv (Vars.ty v) in
      let is_ty_enum = Symbols.TyInfo.is_enum env.table ty_v in
      let is_ty_encodable = Type.is_bitstring_encodable ty_v in
      let adv =
        (* FIXME: could be improved into `info.det && is_ty_enum` *)
        (info.const && is_ty_enum) || 
        (info.const && is_ty_encodable) ||
        info.adv
      in
      {
        const   = info.const        ;
        adv     = adv               ;
        si      = info.system_indep ;
        no_diff = true              ;
        det     = info.const        ;
      }

    | Name _ ->
      let merged = doit_subterms env t in
      { merged with det = false; const = false; adv = false; }

    | Macro _ -> mk_tags ~no_diff:true ()
    (* TODO: multi-terms: once macros are decorated by system
       expressions, this needs to change *)

    | Fun (f,_) -> 
      let is_att = f = Symbols.fs_att || f = Symbols.fs_qatt in
      let is_si = Operator.is_system_indep env.table f in
      {
        const   = not is_att ;
        adv     = true       ;
        si      = is_si      ;
        no_diff = true       ;
        det     = not is_att ;
      }

    | Find (vs, _, _, _) | Quant (_,vs,_) ->
      let vs_tys = List.map (fun v -> Infer.norm_ty ienv (Vars.ty v)) vs in
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
      let const =
        merged.const && fixed_type_binders
      in
      { merged with const; adv; }

    | App _| Action _ | Tuple _ | Proj _ ->
      doit_subterms env t

    | Diff _ ->
      let merged = doit_subterms env t in
      { merged with si = false; no_diff = false; }

    | Let (v,t1,t2) ->
      let tags = to_vars_tags (doit env t1) in
      let venv = Vars.add_vars [v, tags] env.vars in
      let env = Env.update ~vars:venv env in
      doit env t2
  in
  let tags = doit env t in
  { tags with
    si = tags.si; }
  
(*------------------------------------------------------------------*)
let is_system_indep
    ?(ienv:Infer.env = Infer.mk_env ())
    (env : Env.t) (t : Term.term)
  : bool
  =
  (tags_of_term ~ienv env t).si

let is_deterministic
    ?(ienv:Infer.env = Infer.mk_env ())
    (env : Env.t) (t : Term.term)
  : bool
  =
  (tags_of_term ~ienv env t).det

let is_constant
    ?(ienv:Infer.env = Infer.mk_env ())
    (env : Env.t) (t : Term.term) : bool
  =
  (tags_of_term env ~ienv t).const

(*------------------------------------------------------------------*)
let si_or_single_system
    ~(single_systems : System.Single.Set.t option) (* [None] means no information *)
    (tags : tags)                                  (* the tags associated to a term [t] *)
  : bool
  =
  ( single_systems <> None                               &&
    System.Single.Set.cardinal (oget single_systems) = 1 &&
    tags.no_diff)
  || tags.si
  (* a term [t] can be seen as a single term in any single system of
     [single_systems] if:

     - [single_systems] is a singleton and [t] does not use any [diff] 
     - or [t] is system-independent *)

let is_single_term_in_single_systems
    ?(ienv : Infer.env = Infer.mk_env ())
    ~(single_systems : System.Single.Set.t option) (* [None] means no information *)
    (env : Env.t) (t : Term.term)
  : bool
  =
  let tags = tags_of_term ~ienv env t in
  si_or_single_system tags ~single_systems

(** Exported, see `.mli` *)
let is_single_term_in_context
    ?(ienv : Infer.env = Infer.mk_env ())
    ~(context : SE.context)
    (env : Env.t) (t : Term.term)
  : bool
  =
  let tags = tags_of_term ~ienv env t in
  let single_systems = SE.single_systems_of_context context in
  si_or_single_system tags ~single_systems

(** Exported, see `.mli` *)
let is_single_term_in_se
    ?(ienv : Infer.env = Infer.mk_env ())
    ~(se : SE.t list)
    (env : Env.t) (t : Term.term)
  : bool
  =
  let tags = tags_of_term ~ienv env t in
  let single_systems =
    List.fold_left (fun set e ->
        let set' = SE.single_systems_of_se e in
        match set,set' with
        | Some set, Some set' -> System.Single.Set.union set set' |> some
        | _ -> None
      ) (Some System.Single.Set.empty) se
  in
  si_or_single_system tags ~single_systems


(*------------------------------------------------------------------*)
let is_ptime_deducible
    ~(si : bool)
    ?(ienv:Infer.env = Infer.mk_env ())
    (env : Env.t) (t : Term.term) : bool
  =
  let tags = tags_of_term env ~ienv t in
  tags.adv &&
  (not si ||
   let single_systems = SE.single_systems_of_context env.system in
   si_or_single_system tags ~single_systems)

(*------------------------------------------------------------------*)
(** Exported, shadows the previous definition. *)
let tags_of_term
    ?(ienv:Infer.env = Infer.mk_env ())
    (env : Env.t) (t : Term.term)
  : Vars.Tag.t
  =
  let tags = tags_of_term ~ienv env t in
  {
    system_indep = tags.si    ;
    const        = tags.const ;
    adv          = tags.adv   ;
  }
