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
  rewrite : bool;   (** user-defined rewriting rules *)
  delta   : bool;   (** replace defined variables by their body *)
  beta    : bool;   (** β-reduction *)
  proj    : bool;   (** reduce projections *)
  constr  : bool;   (** reduce tautologies over timestamps *)
}

let rp_empty = { 
  rewrite = false;
  beta    = false; 
  delta   = false; 
  proj    = false; 
  constr  = false; 
}

let rp_default = { 
  rewrite = true;
  beta    = true; 
  delta   = false; 
  proj    = true; 
  constr  = false; 
}

let rp_full = { 
  rewrite = true;
  beta    = true; 
  delta   = true; 
  proj    = true; 
  constr  = false; 
}

let parse_simpl_args
    (param : red_param) (args : Args.named_args) : red_param
  =
  let parse_tag param (tag : Symbols.lsymb) =
    match tag with
    | L.{ pl_desc = "rw"     } -> { param with rewrite = true; }
    | L.{ pl_desc = "beta"   } -> { param with beta    = true; }
    | L.{ pl_desc = "delta"  } -> { param with delta   = true; }
    | L.{ pl_desc = "proj"   } -> { param with proj    = true; }
    | L.{ pl_desc = "constr" } -> { param with constr  = true; }

    | l -> Tactics.hard_failure ~loc:(L.loc l) (Failure "unknown argument")
  in

  List.fold_left (fun param arg ->
      match arg with
      | Args.NArg tag -> parse_tag param tag

      | Args.NList (L.{ pl_desc = "flags" }, tags) -> 
        (* set all flags to [false], then parse [tags] *)
        List.fold_left parse_tag rp_empty tags

      | Args.NList (l,_) ->
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

(*------------------------------------------------------------------*)
let conv_ty (ty1 : Type.ty) (ty2 : Type.ty) : unit =
  if not (Type.equal ty1 ty2) then not_conv ()

let conv_tys (tys1 : Type.ty list) (tys2 : Type.ty list) : unit =
  List.iter2 conv_ty tys1 tys2

(*------------------------------------------------------------------*)
let conv_system table (se1 : SE.t) (se2 : SE.t) : unit =
  if not (SE.equal table se1 se2) then not_conv ()

let conv_systems table (l1 : SE.t list) (l2 : SE.t list) : unit =
  List.iter2 (conv_system table) l1 l2

(*------------------------------------------------------------------*)
let conv_applied_ftype
    (ft1 : Term.applied_ftype) (ft2 : Term.applied_ftype) 
  : unit 
  =
  conv_ty  ft1.fty.fty_out  ft2.fty.fty_out;
  conv_tys ft1.fty.fty_args ft2.fty.fty_args;

  List.iter2 (fun tv1 tv2 ->
      if not (tv1 = tv2) then not_conv () (* FIXME: necessary? *)
    ) ft1.fty.fty_vars ft2.fty.fty_vars;

  conv_tys ft1.ty_args ft2.ty_args

(*------------------------------------------------------------------*)
let conv_var (st : cstate) (v1 : Vars.var) (v2 : Vars.var) : unit =
  conv_ty (Vars.ty v1) (Vars.ty v2);
  if not (Vars.equal (Term.subst_var st.subst v1) v2) then not_conv ()

(*------------------------------------------------------------------*)
let conv_bnd (st : cstate) (v1 : Vars.var) (v2 : Vars.var) : cstate =
  if not (Type.equal (Vars.ty v1) (Vars.ty v2)) then not_conv ();
  { st with subst = Term.ESubst (Term.mk_var v1, Term.mk_var v2) :: st.subst }

let conv_bnds (st : cstate) (vs1 : Vars.vars) (vs2 : Vars.vars) : cstate =
  List.fold_left2 conv_bnd st vs1 vs2

(*------------------------------------------------------------------*)
let conv_tagged_bnds
    (st : cstate) (vs1 : Vars.tagged_vars) (vs2 : Vars.tagged_vars) : cstate 
  =
  List.fold_left2 (fun st (v1, tag1) (v2, tag2) -> 
      if tag1 <> tag2 then not_conv ();
      conv_bnd st v1 v2
    ) st vs1 vs2

(*------------------------------------------------------------------*)
let rec conv (st : cstate) (t1 : Term.term) (t2 : Term.term) : unit =
  match t1, t2 with
  | Term.Fun (fs1, app_fty1), Term.Fun (fs2, app_fty2)
    when fs1 = fs2 ->
    conv_applied_ftype app_fty1 app_fty2

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
    if List.length v1 <> List.length v2 then not_conv ();
    conv_l st v1 v2
    
  | Term.Tuple l1, Term.Tuple l2 ->
    if List.length l1 <> List.length l2 then not_conv ();
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

  | Equiv.Atom (Pred p1), Equiv.Atom (Pred p2) when p1.psymb = p2.psymb ->
    conv_tys p1.ty_args p2.ty_args;
    conv_systems st.table p1.se_args p2.se_args;

    List.iter2 (fun (se1,l1) (se2,l2) ->
        assert (SE.equal st.table se1 se2);
        let system = SE.{set = (se1 :> SE.t); pair = None; } in
        conv_l { st with system } l1 l2
      ) p1.multi_args p2.multi_args;

    let system = SE.{set = (SE.of_list [] :> SE.t); pair = None; } in
    conv_l { st with system } p1.simpl_args p2.simpl_args

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

  val expand_head_once_term :
    ?expand_context:Macros.expand_context ->
    ?se:SE.t -> 
    red_param -> t -> Term.term -> Term.term * bool
                                   
  val expand_head_once :
    ?expand_context:Macros.expand_context ->
    ?system:SE.context -> 
    red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a * bool

  val destr_eq : 
    t -> 'a Equiv.f_kind -> 'a -> (Term.term * Term.term) option

  val destr_not : 
    t -> 'a Equiv.f_kind -> 'a -> (Term.term) option

  val destr_or : 
    t -> 'a Equiv.f_kind -> 'a -> ('a * 'a) option

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
    try_red [expand_head_once st;  (* δ *)
             rewrite_head_once st; (* user rewriting rules *)
             reduce_beta st;       (* β *)
             reduce_proj st;       (* proj *)
             reduce_constr st; ]   (* constr *)

  and reduce_beta (st : state) (t : Term.term) : Term.term * bool =
    if not st.param.beta then t, false
    else Match.reduce_beta t

  and reduce_proj (st : state) (t : Term.term) : Term.term * bool =
    if not st.param.proj then t, false
    else Match.reduce_proj t

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
        if Constr.(is_tautology ~exn:NoExp timeout t )
        then Term.mk_true,true
        else if Constr.(is_tautology ~exn:NoExp timeout (Term.mk_not t))
        then Term.mk_false,true
        else t,false   
      with NoExp -> (t,false)
                    
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
    if not st.param.rewrite then t, false 
    else 
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
    | Term.App (Fun (fs, fty), [c;t;e]) when fs = Term.f_ite -> 
      let c, has_red0 = reduce st c in

      let hyps_t = add_hyp c st.hyps in
      let hyps_f = add_hyp (Term.mk_not ~simpl:true c) st.hyps in

      let t, has_red1 = reduce { st with hyps = hyps_t } t in
      let e, has_red2 = reduce { st with hyps = hyps_f } e in

      Term.mk_fun0 fs fty [c; t; e],
      has_red0 || has_red1 || has_red2

    (* [φ => ψ] *)
    | Term.App (Fun (fs, fty), [f1;f2]) when fs = Term.f_impl -> 
      let hyps2 = add_hyp f1 st.hyps in

      let f1, has_red1 = reduce st f1 in
      let f2, has_red2 = reduce { st with hyps = hyps2 } f2 in      

      Term.mk_fun0 fs fty [f1;f2],
      has_red1 || has_red2

    (* [φ && ψ] is handled as [φ && (φ => ψ)] *)
    | Term.App (Fun (fs, fty), [f1;f2]) when fs = Term.f_and -> 
      let hyps2 = add_hyp f1 st.hyps in

      let f1, has_red1 = reduce st f1 in
      let f2, has_red2 = reduce { st with hyps = hyps2 } f2 in      

      Term.mk_fun0 fs fty [f1;f2],
      has_red1 || has_red2

    (* [φ || ψ] is handled as [φ || (¬ φ => ψ)] *)
    | Term.App (Fun (fs, fty), [f1;f2]) when fs = Term.f_or -> 
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
  let expand_head_once_term
      ?(expand_context : Macros.expand_context = InSequent)
      ?(se : SE.arbitrary option)
      (param : red_param) (s : S.t)
      (t : Term.term) : Term.term * bool 
    = 
    let se = odflt (S.system s).set se in
    let state = mk_state ~expand_context ~se (S.vars s) param s in
    expand_head_once state t

  (*------------------------------------------------------------------*)
  (** Exported.
      We need type introspection here. *)
  let expand_head_once (type a) 
      ?(expand_context : Macros.expand_context = InSequent)
      ?(system : SE.context option)
      (param : red_param) (s : S.t)
      (k : a Equiv.f_kind) (x : a) : a * bool
    =
    let se = omap (fun system -> system.SE.set) system in
    match k with
    | Local_t  -> expand_head_once_term ~expand_context ?se param s x
    | Global_t -> x, false
    | Any_t ->
      match x with
      | Local  x -> 
        let x, has_red = expand_head_once_term ~expand_context ?se param s x in
        Local x, has_red

      | Global _ -> x, false
      
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
        let e_se = (oget system.pair :> SE.t) in
        let state = mk_state ~expand_context ~se:e_se env param s in

        let e = List.map (fst -| reduce state) e in
        Equiv.Atom (Equiv.Equiv e)

      | Equiv.Atom (Pred pa) ->
        let simpl_args =
          let se = (SE.of_list [] :> SE.t) in
          let state = mk_state ~expand_context ~se env param s in
          List.map (fst -| reduce state) pa.simpl_args
        in
        let multi_args =
          List.map (fun (se,args) ->
              let state = mk_state ~expand_context ~se env param s in
              ( se, List.map (fst -| reduce state) args )
            ) pa.multi_args
        in
        Equiv.Atom (Equiv.Pred { pa with simpl_args; multi_args; })
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
  (* Destruct [x] according to an arbitrary destruct function [destr_f], 
     using [s] to reduce [x] if necessary. *)
  let mk_destr (type a)
      (destr_f : Term.term -> 'b option)
      ?(se : SE.arbitrary option)
      (s : S.t) (k : a Equiv.f_kind)
      (x : a) : 'b option
    =
    let rec destr_term (x : Term.term) =
      match destr_f x with
      | Some _ as res -> res
      | None ->
        let x, has_red = expand_head_once_term ?se rp_full s x in
        if not has_red then 
          None                  (* did not reduce, failed *)
        else
          destr_term x          (* reduced, recurse to try again *)
    in
    let destr_equiv (x : Equiv.form) = obind destr_term (Equiv.destr_reach x) in

    match k with
    | Local_t  -> destr_term  x
    | Global_t -> destr_equiv x
    | Any_t ->
      match x with
      | Local x  -> destr_term  x
      | Global x -> destr_equiv x

  (*------------------------------------------------------------------*)
  (* Similar to [mk_destr], but with a dependent return type and
     two different destruct functions. *)
  let mk_destr_k (type a)
      (destr_t0 : Term.term  -> (Term.term  * Term.term ) option)
      (destr_e  : Equiv.form -> (Equiv.form * Equiv.form) option)
      ?(se : SE.arbitrary option)
      (s : S.t) (k : a Equiv.f_kind)
      (x : a) : (a * a) option
    =
    let rec destr_t (x : Term.term) =
      match destr_t0 x with
      | Some _ as res -> res
      | None ->
        let x, has_red = expand_head_once_term ?se rp_full s x in
        if not has_red then 
          None               (* did not reduce, failed *)
        else
          destr_t x          (* reduced, recurse to try again *)
    in

    match k with
    | Local_t  -> destr_t x
    | Global_t -> destr_e x
    | Any_t ->
      match x with
      | Local x  -> omap (fun (a,b) -> Equiv.Local  a, Equiv.Local  b) (destr_t x)
      | Global x -> omap (fun (a,b) -> Equiv.Global a, Equiv.Global b) (destr_e x)

  (*------------------------------------------------------------------*)
  let destr_eq (type a)
      (s : S.t) (k : a Equiv.f_kind)
      (x : a) : (Term.term * Term.term) option
    =
    let destr_eq_or_iff x =
      match Term.destr_eq x with
      | Some _ as res -> res
      | None -> Term.destr_iff x
    in
    mk_destr destr_eq_or_iff s k x

  let destr_not (type a)
      (s : S.t) (k : a Equiv.f_kind)
      (x : a) : Term.term option
    =
    mk_destr Term.destr_not s k x

  (*------------------------------------------------------------------*)
  let destr_or (type a)
      (s : S.t) (k : a Equiv.f_kind)
      (x : a) : (a * a) option
    =
    mk_destr_k Term.destr_or (Equiv.Smart.destr_or ~env:(S.env s)) s k x

  (*------------------------------------------------------------------*)
  let destr_and (type a)
      (s : S.t) (k : a Equiv.f_kind)
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
    mk_destr_k destr_and Equiv.Smart.destr_and s k x

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

