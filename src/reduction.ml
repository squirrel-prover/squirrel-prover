open Utils

module L = Location
module SE = SystemExpr
module Args = TacticsArgs
module THyps = Hyps.TraceHyps

(*------------------------------------------------------------------*)
let rev_subst subst = 
  List.map (fun (Term.ESubst (u,v)) -> Term.ESubst (v,u)) subst

(*------------------------------------------------------------------*)
type red_param = { 
  delta  : bool;
  beta   : bool;
  constr : bool;
}

let rp_default = { beta = true; delta = false; constr = false; }

let rp_full = { beta = true; delta = true; constr = false; }

let parse_simpl_args
    (param : red_param) (args : Args.named_args) : red_param
  =
  List.fold_left (fun param arg ->
      match arg with
      | Args.NArg l ->
        if Location.unloc l = "constr" then { param with constr = true; }
        else
          Tactics.hard_failure ~loc:(L.loc l) (Failure "unknown argument")
    ) param args


(*------------------------------------------------------------------*)
(** {2 Conversion} *)

(** Conversion state *)
(* FEATURE: conversion modulo *)
type cstate = { 
  table   : Symbols.table;
  system  : SE.context;
  param   : red_param;
  hyps    : THyps.hyps;

  subst   : Term.subst;
  (** pending variable to variable substitution (left -> right) *)

  expand_context : Macros.expand_context;
  (** expantion mode for macros. See [Macros.expand_context]. *)
}


(** Make a cstate directly *)
let mk_cstate 
    ?(system = SystemExpr.context_any)
    ?(expand_context = Macros.InSequent)
    ?(hyps = THyps.empty)
    ?(param = rp_default)
    table 
  : cstate 
  =
  { table; system; param; hyps; expand_context;
    subst = []; }

(*------------------------------------------------------------------*)
(** Internal *)
exception NotConv

let not_conv () = raise NotConv

let conv_ty (ty1 : Type.ty) (ty2 : Type.ty) : unit =
  if not (Type.equal ty1 ty2) then not_conv ()

let conv_tys (tys1 : Type.ty list) (tys2 : Type.ty list) : unit =
  List.iter2 conv_ty tys1 tys2

let conv_ftype (ft1 : Type.ftype) (ft2 : Type.ftype) : unit =
  conv_ty  ft1.fty_out  ft2.fty_out;
  conv_tys ft1.fty_args ft2.fty_args;
  List.iter2 (fun tv1 tv2 ->
      if not (tv1 = tv2) then not_conv ()
    ) ft1.fty_vars ft2.fty_vars

let conv_var (st : cstate) (v1 : Vars.var) (v2 : Vars.var) : unit =
  if not (Type.equal (Vars.ty v1) (Vars.ty v2)) then not_conv ();
  if not (Vars.equal (Term.subst_var st.subst v1) v2) then not_conv ()

let conv_bnd (st : cstate) (v1 : Vars.var) (v2 : Vars.var) : cstate =
  if not (Type.equal (Vars.ty v1) (Vars.ty v2)) then not_conv ();
  { st with subst = Term.ESubst (Term.mk_var v1, Term.mk_var v2) :: st.subst }

let conv_bnds (st : cstate) (vs1 : Vars.vars) (vs2 : Vars.vars) : cstate =
  List.fold_left2 conv_bnd st vs1 vs2

let conv_tagged_bnds (st : cstate) (vs1 : Vars.tagged_vars) (vs2 : Vars.tagged_vars) : cstate =
  List.fold_left2 (fun st (v1, _) (v2, _) -> conv_bnd st v1 v2) st vs1 vs2

let rec conv (st : cstate) (t1 : Term.term) (t2 : Term.term) : unit =
  match t1, t2 with
  | Term.Fun (fs1, fty1, l1), Term.Fun (fs2, fty2, l2)
    when fs1 = fs2 ->
    conv_ftype fty1 fty2;
    conv_l st l1 l2

  | Term.Name (ns1,l1), Term.Name (ns2,l2) when ns1.s_symb = ns2.s_symb ->
    assert (ns1.Term.s_typ = ns2.Term.s_typ);
    conv_l st l1 l2

  | Term.Action (a1, is1), Term.Action (a2, is2) when a1 = a2 ->
    conv_l st is1 is2

  | Term.Diff (Explicit l1), Term.Diff (Explicit l2) ->
    List.iter2 (fun (p1, t1) (p2, t2) ->
        if p1 <> p2 then not_conv ();
        conv st t1 t2
      ) l1 l2

  | Term.Macro (ms1, terms1, ts1), Term.Macro (ms2, terms2, ts2)
    when ms1.s_symb = ms2.s_symb ->
    assert (ms1.Term.s_typ = ms2.Term.s_typ);
    conv_l st (ts1 :: terms1) (ts2 :: terms2)

  | Term.Quant  (q, is1, t1), Term.Quant (q', is2, t2) when q = q' ->
    if List.length is1 <> List.length is2 then not_conv ();
    let st = conv_bnds st is1 is2 in
    conv st t1 t2

  | Term.Find (is1, c1, t1, e1), Term.Find (is2, c2, t2, e2) ->
    if List.length is1 <> List.length is2 then not_conv ();
    let st' = conv_bnds st is1 is2 in
    conv_l st' [c1; t1] [c2; t2];
    conv st e1 e2

  | Term.Var v1, Term.Var v2 -> conv_var st v1 v2

  | Term.App (u1, v1), Term.App (u2, v2) ->
    conv st u1 u2;
    conv_l st v1 v2
    
  | Term.Tuple l1, Term.Tuple l2 ->
    conv_l st l1 l2

  | Term.Proj (i1, t1), Term.Proj (i2, t2) ->
    if i1 <> i2 then not_conv ();
    conv st t1 t2
    
  | _, _ -> not_conv ()

and conv_l (st : cstate) (ts1 : Term.terms) (ts2 : Term.terms) : unit =
  List.iter2 (conv st) ts1 ts2

let rec conv_e (st : cstate) (e1 : Equiv.form) (e2 : Equiv.form) : unit =
  match e1, e2 with
  | Equiv.Quant (q1, vs1, e1), Equiv.Quant (q2, vs2, e2) when q1 = q2 ->
    if List.length vs1 <> List.length vs2 then not_conv ();
    let st = conv_tagged_bnds st vs1 vs2 in
    conv_e st e1 e2

  | Equiv.And  (el1, er1), Equiv.And  (el2, er2)
  | Equiv.Or   (el1, er1), Equiv.Or   (el2, er2)
  | Equiv.Impl (el1, er1), Equiv.Impl (el2, er2)->
    conv_e_l st [el1; er1] [el2; er2]

  | Equiv.Atom (Reach f1), Equiv.Atom (Reach f2) ->
    let system = SE.{set = st.system.set; pair = None; } in
    conv { st with system } f1 f2

  | Equiv.Atom (Equiv ts1), Equiv.Atom (Equiv ts2) ->
    let system =
      SE.{set = (oget st.system.pair :> SE.arbitrary); pair = None; }
    in
    conv_l { st with system } ts1 ts2

  | _, _ -> not_conv ()

and conv_e_l
    (st : cstate) (es1 : Equiv.form list) (es2 : Equiv.form list) : unit
  =
  List.iter2 (conv_e st) es1 es2


(*------------------------------------------------------------------*)
(** Exported *)
let conv (s : cstate) (t1 : Term.term) (t2 : Term.term) : bool =
  try conv s t1 t2; true with NotConv -> false

(** Exported *)
let conv_e (s : cstate) (t1 : Equiv.form) (t2 : Equiv.form) : bool =
  try conv_e s t1 t2; true with NotConv -> false

(*------------------------------------------------------------------*)
module type S = sig
  type t                        (* type of sequent *)

  (*------------------------------------------------------------------*)
  (** {2 reduction } *)

  val reduce_term : 
    ?expand_context:Macros.expand_context ->
    ?se:SE.t -> red_param -> t -> Term.term -> Term.term     

  val reduce_equiv : 
    ?expand_context:Macros.expand_context ->
    ?system:SE.context -> red_param -> t -> Equiv.form -> Equiv.form

  val reduce : 
    ?expand_context:Macros.expand_context ->
    ?system:SE.context -> red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a

  (*------------------------------------------------------------------*)
  (** {2 expantion and destruction modulo } *)

  val expand_head_once :
    ?expand_context:Macros.expand_context ->
    ?se:SE.t -> 
    red_param -> t -> Term.term -> Term.term * bool

  val destr_eq : 
    t -> 'a Equiv.f_kind -> 'a -> (Term.term * Term.term) option

  val destr_not : 
    t -> 'a Equiv.f_kind -> 'a -> (Term.term) option

  val destr_and : 
    t -> 'a Equiv.f_kind -> 'a -> ('a * 'a) option

  (*------------------------------------------------------------------*)
  (** {2 conversion } *)

  val conv_term  :
    ?expand_context:Macros.expand_context -> 
    ?se:SE.t -> 
    ?param:red_param ->
    t ->
    Term.term -> Term.term -> bool

  val conv_equiv : 
    ?expand_context:Macros.expand_context ->
    ?system:SE.context -> 
    ?param:red_param ->
    t ->
    Equiv.form -> Equiv.form -> bool

  val conv_kind : 
    ?expand_context:Macros.expand_context ->
    ?system:SE.context -> 
    ?param:red_param ->
    t -> 'a Equiv.f_kind ->
    'a -> 'a -> bool
end

(*------------------------------------------------------------------*)
module Mk (S : LowSequent.S) : S with type t := S.t = struct
  type state = { 
    table   : Symbols.table;
    env     : Vars.env;         (* used to get variable tags *)
    sexpr   : SE.arbitrary;
    param   : red_param;
    hyps    : THyps.hyps;

    expand_context : Macros.expand_context;
    (** expantion mode for macros. See [Macros.expand_context]. *)
  }

  (*------------------------------------------------------------------*)
  let add_hyp (f : Term.term) hyps : THyps.hyps =
    THyps.add TacticsArgs.AnyName (Local f) hyps

  (*------------------------------------------------------------------*)  
  (** Internal *)
  exception NoExp 

  (* Invariant: we must ensure that fv(reduce(u)) ⊆ fv(t)
     Return: reduced term, reduction occurred *)
  (* FEATURE: memoisation? *)
  let rec reduce (st : state) (t : Term.term) : Term.term * bool = 
    let t, has_red = reduce_head_once st t in

    if has_red then fst (reduce st t), true
    else
      let t, has_red = reduce_subterms st t in
      if has_red then fst (reduce st t), true
      else t, false

  (* Reduce once at head position *)
  and reduce_head_once (st : state) (t : Term.term) : Term.term * bool = 
    let rec try_red red_funcs =
      match red_funcs with
      | [] -> t, false
      | red_f :: red_funcs ->
        let t, has_red = red_f t in
        if has_red then t, true
        else try_red red_funcs
    in
    try_red [expand_head_once st; 
             rewrite_head_once st;
             Match.reduce_beta;
             Match.reduce_proj;
             reduce_constr st; ]

  (* Try to show using [Constr] that [t] is [false] or [true] *)
  and reduce_constr (st : state) (t : Term.term) : Term.term * bool =
    if not st.param.constr ||
       Term.ty t <> Type.Boolean ||
       Term.equal t Term.mk_false ||
       Term.equal t Term.mk_true
    then t, false
    else
      try
        let timeout = TConfig.solver_timeout st.table in
        if not Constr.(m_is_sat (models_conjunct timeout ~exn:NoExp [t]))
        then Term.mk_false, true
        else if not Constr.(m_is_sat (models_conjunct timeout ~exn:NoExp [Term.mk_not t]))
        then Term.mk_true, true
        else t, false
      with NoExp -> t, false

  (* Expand once at head position *)
  and expand_head_once (st : state) (t : Term.term) : Term.term * bool = 
    if not st.param.delta then t, false 
    else 
      try 
        Match.expand_head_once 
          ~mode:st.expand_context ~exn:NoExp
          st.table st.sexpr (lazy st.hyps) t
      with NoExp -> t, false

  (* Rewrite once at head position *)
  and rewrite_head_once (st : state) (t : Term.term) : Term.term * bool = 
    let db = Hint.get_rewrite_db st.table in
    let hints = Term.Hm.find_dflt [] (Term.get_head t) db in

    let rule = List.find_map (fun Hint.{ rule } ->
        match 
          Rewrite.rewrite_head
            st.table st.env st.expand_context (lazy st.hyps) st.sexpr 
            rule t 
        with
        | None -> None
        | Some (red_t, subs) ->
          let subs_valid =  
            List.for_all (fun (sexpr, sub) -> 
                (* FEATURE: conversion *)
                fst (reduce { st with sexpr; param = rp_default } sub) = 
                Term.mk_true
              ) subs 
          in              
          if subs_valid then Some red_t else None            
      ) hints
    in

    match rule with
    | None -> t, false
    | Some red_t -> red_t, true

  (* Reduce all strict subterms *)
  and reduce_subterms (st : state) (t : Term.term) : Term.term * bool = 
    match t with
    | Term.Quant (q, evs, t0) -> 
      let _, subst = Term.refresh_vars evs in
      let t0 = Term.subst subst t0 in
      let red_t0, has_red =
        let env = Vars.add_vars (Vars.Tag.local_vars evs) st.env in
        reduce { st with env } t0
      in

      if not has_red then t, false
      else
        let r_subst = rev_subst subst in
        let red_t0 = Term.subst r_subst red_t0 in
        let red_t = Term.mk_quant ~simpl:false q evs red_t0 in
        red_t, true

    (* if-then-else *)
    | Term.Fun (fs, fty, [c;t;e]) when fs = Term.f_ite -> 
      let c, has_red0 = reduce st c in

      let hyps_t = add_hyp c st.hyps in
      let hyps_f = add_hyp (Term.mk_not ~simpl:true c) st.hyps in

      let t, has_red1 = reduce { st with hyps = hyps_t } t in
      let e, has_red2 = reduce { st with hyps = hyps_f } e in

      Term.mk_fun0 fs fty [c; t; e],
      has_red0 || has_red1 || has_red2

    (* [φ => ψ] *)
    | Term.Fun (fs, fty, [f1;f2]) when fs = Term.f_impl -> 
      let hyps2 = add_hyp f1 st.hyps in

      let f1, has_red1 = reduce st f1 in
      let f2, has_red2 = reduce { st with hyps = hyps2 } f2 in      

      Term.mk_fun0 fs fty [f1;f2],
      has_red1 || has_red2

    (* [φ && ψ] is handled as [φ && (φ => ψ)] *)
    | Term.Fun (fs, fty, [f1;f2]) when fs = Term.f_and -> 
      let hyps2 = add_hyp f1 st.hyps in

      let f1, has_red1 = reduce st f1 in
      let f2, has_red2 = reduce { st with hyps = hyps2 } f2 in      

      Term.mk_fun0 fs fty [f1;f2],
      has_red1 || has_red2

    (* [φ || ψ] is handled as [φ || (¬ φ => ψ)] *)
    | Term.Fun (fs, fty, [f1;f2]) when fs = Term.f_or -> 
      let hyps2 = add_hyp (Term.mk_not f1) st.hyps in

      let f1, has_red1 = reduce st f1 in
      let f2, has_red2 = reduce { st with hyps = hyps2 } f2 in      

      Term.mk_fun0 fs fty [f1;f2],
      has_red1 || has_red2

    | Term.Find (is, c, t, e) -> 
      let _, subst = Term.refresh_vars is in
      let c, t = Term.subst subst c, Term.subst subst t in
      let st1 =
        let env = Vars.add_vars (Vars.Tag.local_vars is) st.env in
        { st with env }
      in

      let c, has_red0 = reduce st1 c in

      let hyps_t = add_hyp c st.hyps in
      let hyps_f =
        add_hyp (Term.mk_forall is (Term.mk_not ~simpl:true c)) st.hyps
      in

      let t, has_red1 = reduce { st1 with hyps = hyps_t } t in
      let e, has_red2 = reduce { st  with hyps = hyps_f } e in

      let r_subst = rev_subst subst in
      let c, t = Term.subst r_subst c, Term.subst r_subst t in

      Term.mk_find ~simpl:true is c t e,
      has_red0 || has_red1 || has_red2

    | Term.Diff (Explicit l) -> 
      let has_red, l = 
        List.map_fold (fun has_red (label,t) -> 
            let st = { st with sexpr = SE.project [label] st.sexpr } in
            let t, has_red' = reduce st t in
            has_red || has_red', (label, t)
          ) false l
      in
      Term.mk_diff l, has_red

    | Term.Proj   _
    | Term.App    _ 
    | Term.Tuple  _
    | Term.Macro  _
    | Term.Name   _
    | Term.Fun    _
    | Term.Action _
    | Term.Var    _ -> 
      let has_red, t = 
        Term.tmap_fold (fun has_red t -> 
            let t, has_red' = reduce st t in
            has_red || has_red', t
          ) false t
      in
      t, has_red

  (*------------------------------------------------------------------*)
  (** [se] is the system of the term being reduced. *)
  (* computation must be fast *)
  let mk_state ~expand_context ~se (env : Vars.env) (param : red_param) (s : S.t) : state = 
    { table = S.table s;
      sexpr = se;
      env;
      param;
      hyps = S.get_trace_hyps s; 
      expand_context; } 

  (*------------------------------------------------------------------*)
  (** Exported. *)
  let expand_head_once
      ?(expand_context : Macros.expand_context = InSequent)
      ?(se : SE.arbitrary option)
      (param : red_param) (s : S.t)
      (t : Term.term) : Term.term * bool 
    = 
    let se = odflt (S.system s).set se in
    let state = mk_state ~expand_context ~se (S.vars s) param s in
    expand_head_once state t
      
  (*------------------------------------------------------------------*)
  (** Exported. *)
  let reduce_term
      ?(expand_context : Macros.expand_context = InSequent)
      ?(se : SE.arbitrary option)
      (param : red_param) (s : S.t)
      (t : Term.term) : Term.term 
    = 
    let se = odflt (S.system s).set se in
    let state = mk_state ~expand_context ~se (S.vars s) param s in
    let t, _ = reduce state t in
    t

  (** Exported. *)
  let reduce_equiv
      ?(expand_context : Macros.expand_context = InSequent)
      ?(system : SE.context option)
      (param : red_param) (s : S.t) (e : Equiv.form) : Equiv.form 
    =
    let system = odflt (S.system s) system in
    
    let rec reduce_e (env : Vars.env) (e : Equiv.form) : Equiv.form =
      match e with
      | Equiv.Quant (q, vs, e) -> 
        let _, subst = Term.refresh_vars_w_info vs in
        let e = Equiv.subst subst e in
        let red_e =
          let env = Vars.add_vars vs env in
          reduce_e env e
        in

        let r_subst = rev_subst subst in
        let red_e = Equiv.subst r_subst red_e in
        Equiv.Quant (q, vs, red_e)

      | Equiv.And (e1, e2) ->
        Equiv.And (reduce_e env e1, reduce_e env e2)

      | Equiv.Or (e1, e2) ->
        Equiv.Or (reduce_e env e1, reduce_e env e2)

      | Equiv.Impl (e1, e2) ->
        Equiv.Impl (reduce_e env e1, reduce_e env e2)

      | Equiv.Atom (Reach f) ->
        let state = mk_state ~expand_context ~se:system.set env param s in
        let f, _ = reduce state f in
        Equiv.Atom (Reach f)

      | Equiv.Atom (Equiv e) ->
        let e_se = (oget system.pair :> SE.arbitrary) in
        let state = mk_state ~expand_context ~se:e_se env param s in

        let e = List.map (fst -| reduce state) e in
        Equiv.Atom (Equiv.Equiv e)
    in
    reduce_e (S.vars s) e
      
  (** We need type introspection there *)
  let reduce (type a) 
      ?(expand_context : Macros.expand_context = InSequent)
      ?(system : SE.context option)
      (param : red_param) (s : S.t) (k : a Equiv.f_kind) (x : a) : a 
    =
    let se = omap (fun system -> system.SE.set) system in
    match k with
    | Local_t  -> reduce_term  ~expand_context ?se     param s x
    | Global_t -> reduce_equiv ~expand_context ?system param s x
    | Any_t ->
      match x with
      | Local x   -> Local (reduce_term  ~expand_context ?se     param s x)
      | Global x -> Global (reduce_equiv ~expand_context ?system param s x)

 (*------------------------------------------------------------------*)
  (* FEATURE: use [s] to reduce [x] if necessary *)
  let destr_eq (type a)
      (_ : S.t) (k : a Equiv.f_kind)
      (x : a) : (Term.term * Term.term) option
    =
    let destr_eq x =
      match Term.destr_eq x with
      | Some _ as res -> res
      | None -> Term.destr_iff x
    in
    let e_destr_eq x = obind destr_eq (Equiv.destr_reach x) in

    match k with
    | Local_t  ->   destr_eq x
    | Global_t -> e_destr_eq x
    | Any_t ->
      match x with
      | Local x  ->   destr_eq x
      | Global x -> e_destr_eq x

  (* FEATURE: use [s] to reduce [x] if necessary *)
  let destr_not (type a)
      (_ : S.t) (k : a Equiv.f_kind)
      (x : a) : Term.term option
    =
    let e_destr_not x = obind Term.destr_not (Equiv.destr_reach x) in

    match k with
    | Local_t  -> Term.destr_not x
    | Global_t ->    e_destr_not x
    | Any_t ->
      match x with
      | Local x  -> Term.destr_not x
      | Global x ->    e_destr_not x

  (* FEATURE: use [s] to reduce [x] if necessary *)
  let destr_and (type a)
      (_ : S.t) (k : a Equiv.f_kind)
      (x : a) : (a * a) option
    =
    let destr_and x =
      match Term.destr_and x with
      | Some _ as res -> res
      | None ->
        match Term.destr_iff x with
        | Some (t1, t2) ->
          Some (Term.mk_impl ~simpl:false t1 t2,
                Term.mk_impl ~simpl:false t2 t1)
            
        | None -> None
    in
    let e_destr_and x = Equiv.Smart.destr_and x in

    match k with
    | Local_t  ->   destr_and x
    | Global_t -> e_destr_and x
    | Any_t ->
      match x with
      | Local x ->
        omap (fun (x,y) -> Equiv.Local x, Equiv.Local y) (destr_and x)
      | Global x ->
        omap (fun (x,y) -> Equiv.Global x, Equiv.Global y) (e_destr_and x)

  (*------------------------------------------------------------------*)
  (** Make a cstate from a sequent *)
  let cstate_of_seq
      (expand_context : Macros.expand_context)
      (system : SE.context) 
      (param : red_param) (s : S.t) : cstate 
    =
    { table   = S.table s;
      system;
      param;
      hyps    = S.get_trace_hyps s; 
      expand_context;
      subst   = []; } 
  
  (*------------------------------------------------------------------*)
  (** Exported. *)
  let conv_term
      ?(expand_context : Macros.expand_context = InSequent)
      ?(se : SE.arbitrary option)
      ?(param : red_param = rp_default)
      (s : S.t)
      (t1 : Term.term) (t2 : Term.term) : bool
    =
    let se = odflt (S.system s).set se in
    let system = SE.{set = se; pair = None; } in
    let state = cstate_of_seq expand_context system param s in
    conv state t1 t2

  (** Exported. *)
  let conv_equiv
      ?(expand_context : Macros.expand_context = InSequent)
      ?(system : SE.context option)
      ?(param : red_param = rp_default)
      (s : S.t)
      (e1 : Equiv.form) (e2 : Equiv.form) : bool
    =
    let system = odflt (S.system s) system in
    let state = cstate_of_seq expand_context system param s in
    conv_e state e1 e2

  (** We need type introspection there *)
  let conv_kind (type a) 
      ?(expand_context : Macros.expand_context = InSequent)
      ?(system : SE.context option)
      ?(param : red_param = rp_default)
      (s : S.t) (k : a Equiv.f_kind)
      (x1 : a) (x2 : a) : bool
    =
    let se = omap (fun system -> system.SE.set) system in
    match k with
    | Local_t  -> conv_term  ~expand_context ?se     ~param s x1 x2
    | Global_t -> conv_equiv ~expand_context ?system ~param s x1 x2
    | Any_t ->
      match x1, x2 with
      | Local  x1, Local  x2 -> conv_term  ~expand_context ?se     ~param s x1 x2
      | Global x1, Global x2 -> conv_equiv ~expand_context ?system ~param s x1 x2
      | _, _ -> false

end

