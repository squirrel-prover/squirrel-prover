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
        (* The environment look-up fails if we did not give a complete environment.
           Anyhow, it is always sound to return [false]. *)
      end

    | Name _ | Macro _ -> false
    | Fun (f, _) when f = Symbols.fs_att -> false

    | Find (vs, _, _, _) 
    | Quant (_,vs,_) as t ->
      let env = Vars.add_vars (Vars.Tag.global_vars ~const:true vs) venv in
      Term.tforall (is_det env) t
        
    (* recurse *)
    | Let _ | App _ |Fun _ | Action _ | Tuple _ | Proj _ | Diff _ as t ->
      Term.tforall (is_det venv) t
  in
  is_det env.vars t

(*------------------------------------------------------------------*)
let is_constant (env : Env.t) (t : Term.term) : bool =
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

    | Fun (f, _) -> 
      if f = Symbols.fs_att then false else true

    | Find (vs, _, _, _) | Quant (_,vs,_) as t ->
      let fixed_type_binders =
        List.for_all (fun v -> 
            Symbols.TyInfo.is_fixed env.table (Vars.ty v)
          ) vs 
      in
      if not fixed_type_binders then false else
        let venv = Vars.add_vars (Vars.Tag.global_vars ~const:true vs) venv in
        Term.tforall (is_const venv) t
        
    (* recurse *)
    | Let _ | App _ | Action _ | Tuple _ | Proj _ | Diff _ as t ->
      Term.tforall (is_const venv) t
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

    | Fun (fs, _) as t ->
      Operator.is_system_indep env.table fs &&
      Term.tforall (is_si env) t

    | Find (vs, _, _, _) | Quant (_,vs,_) as t ->
      let env = 
        Env.update
          ~vars:(Vars.add_vars (Vars.Tag.global_vars ~const:true vs) env.vars) 
          env
      in
      Term.tforall (is_si env) t

    (* recurse *)
    (* notice that [Action _] is allowed, since we check the independence of the system 
       among all compatible systems. *)
    | Let _ | Name _ | App _ | Action _ | Tuple _ | Proj _ as t ->
      Term.tforall (is_si env) t
  in
  (* a term is system-independent if it applies to a single system (for 
     both set and pair), or if it uses only system-independent constructs *)
  SE.is_single_system env.system || is_si env t

(*------------------------------------------------------------------*)
let is_ptime_deducible ~(si:bool) (env : Env.t) (t : Term.term) : bool =
  let rec is_adv (venv : Vars.env): Term.term -> bool = function
    | Var v ->
      (* check that the variable is constant, fixed and finite
         FEATURE: we could check instead that the type contains elements at-most
         polynomial sized. *)
      let is_constant_fixed_finite =
        try
          let info = Vars.get_info v venv in
          info.const &&
          Symbols.TyInfo.is_fixed  env.table (Vars.ty v) &&
          Symbols.TyInfo.is_finite env.table (Vars.ty v) 
        with Not_found -> false (* sound though possibly inprecise *)
      in
      (* const + encodable as bit-strings => adv *)
      let is_const_base_type =
        try
          let info = Vars.get_info v venv in
          info.const && Type.is_bitstring_encodable (Vars.ty v)
        with Not_found -> false 
      in
      let is_adv =
        try (Vars.get_info v venv).adv with 
        | Not_found -> false 
      in
      is_constant_fixed_finite || is_const_base_type || is_adv

    | Name _ | Macro _ -> false

    | Fun _ -> true

    | Quant ((Lambda | Seq),vs,_) as t ->
      let venv = Vars.add_vars (Vars.Tag.global_vars ~const:true ~adv:true vs) venv in
      Term.tforall (is_adv venv) t

    | Find (vs, _, _, _) | Quant ((ForAll | Exists),vs,_) as t ->
      (* fixed + finite => enumerable in polynomial time
         (though we could be more precise with another type information) *)
      let poly_card_type_binders =
        List.for_all (fun v -> 
            Symbols.TyInfo.is_fixed  env.table (Vars.ty v) &&
            Symbols.TyInfo.is_finite env.table (Vars.ty v) 
          ) vs 
      in
      if not poly_card_type_binders then false else
        let venv = Vars.add_vars (Vars.Tag.global_vars ~const:true ~adv:true vs) venv in
        Term.tforall (is_adv venv) t
        
    (* recurse *)
    | Let _ | App _ | Action _ | Tuple _ | Proj _ | Diff _ as t ->
      Term.tforall (is_adv venv) t
  in
  is_adv env.vars t &&
  (not si || is_system_indep env t) 

(*------------------------------------------------------------------*)
let tag_of_term (env : Env.t) (t : Term.term) : Vars.Tag.t =
  let const        = is_constant                  env t in
  let adv          = is_ptime_deducible ~si:false env t in
  let system_indep = is_system_indep              env t in
  (* latter test checks if [t] is a single system term *)
  { system_indep; const; adv }
