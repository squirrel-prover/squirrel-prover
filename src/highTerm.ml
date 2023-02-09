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
let is_deterministic (env : Env.t) (t : Term.term) : bool =
  let rec is_det (venv : Vars.env): Term.term -> bool = function
    | Var v ->
      begin
        try
          let info = Vars.get_info v venv in
          info.const            (* const => det, so this is sound *)
        with Not_found -> false
        (* The environment look-up fails if we did give a complete environment.
           Anyhow, it is always sound to return [false]. *)
      end

    | Name _ | Macro _ -> false
    | Fun (f, _, _) when f = Symbols.fs_att -> false

    | Find (vs, _, _, _) 
    | Quant (_,vs,_) as t ->
      let env = Vars.add_vars (Vars.Tag.global_vars ~const:true vs) venv in
      Term.tforall (is_det env) t
        
    | t -> Term.tforall (is_det venv) t
  in
  is_det env.vars t

(*------------------------------------------------------------------*)
let is_constant
    (mode : [`Exact | `Approx]) (env : Env.t) (t : Term.term) : bool
  =
  let rec is_const (venv : Vars.env): Term.term -> bool = function
    | Var v ->
      begin
        try
          let info = Vars.get_info v venv in
          info.const
        with Not_found -> false
        (* The environment look-up fails if we did give a complete environment.
           Anyhow, it is always sound to return [false]. *)
      end

    | Name _ | Macro _ -> false
    | Fun (f, _, _) when f = Symbols.fs_att -> false

    | Find (vs, _, _, _) 
    | Quant (_,vs,_) as t when
        List.for_all (fun v -> 
            Symbols.TyInfo.is_fixed  env.table (Vars.ty v)
          ) vs ->
      let venv = Vars.add_vars (Vars.Tag.global_vars ~const:true vs) venv in
      ( mode = `Exact ||
        List.for_all (fun v -> 
            Symbols.TyInfo.is_finite env.table (Vars.ty v)) vs
      ) &&
      Term.tforall (is_const venv) t
        
    | t -> Term.tforall (is_const venv) t
  in
  is_const env.vars t

(*------------------------------------------------------------------*)
let is_system_indep (env : Env.t) (t : Term.term) : bool =
  (* check if a term is system-independent because it uses no system-dependent 
     constructions. *)
  let rec is_si (env : Env.t) : Term.term -> bool = function
    | Var v ->
      begin
        try
          let info = Vars.get_info v env.vars in
          info.system_indep
        with Not_found -> false
        (* The environment look-up fails if we did give a complete environment.
           Anyhow, it is always sound to return [false]. *)
      end

    | Diff _ | Macro _ -> false
    (* FEATURE: this could be made more precise in case we
       are considering a single system (or if the diff is spurious) *)

    | Fun (fs, _, _) as t ->
      Operator.is_system_indep env.table fs &&
      Term.tforall (is_si env) t

    | Find (vs, _, _, _) 
    | Quant (_,vs,_) as t ->
      let env = 
        Env.update
          ~vars:(Vars.add_vars (Vars.Tag.global_vars ~const:true vs) env.vars) 
          env
      in
      Term.tforall (is_si env) t

    | t -> Term.tforall (is_si env) t
  in
  (* a term is system-independent if it applies to a single system (for 
     both set and pair), or if it uses only system-independent constructs *)
  SE.is_single_system env.system || is_si env t


(*------------------------------------------------------------------*)
let is_ptime_deducible
    ~(const : [`Exact | `Approx]) ~(si:bool) (env : Env.t) (t : Term.term) : bool
  =
  is_constant const env t &&
  (not si || is_system_indep env t) &&
  true                          (* TODO: det: ptime: check PTIME *)
