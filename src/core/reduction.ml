open Utils

module L = Location

include ReductionCore

(*------------------------------------------------------------------*)
let rev_subst subst = 
  List.map (fun (Term.ESubst (u,v)) -> Term.ESubst (v,u)) subst

(*------------------------------------------------------------------*)
(** {2 Core reduction functions} *)

module Core (* : ReductionCore.S *) = struct

  (*------------------------------------------------------------------*)
  let parse_simpl_args
      (param : red_param) (args : Args.named_args) : red_param
    =
    let parse_tag param (tag : Symbols.lsymb) =
      match tag with
      | L.{ pl_desc = "rw"     } -> { param with rewrite = true; }
      | L.{ pl_desc = "beta"   } -> { param with beta    = true; }
      | L.{ pl_desc = "zeta"   } -> { param with zeta    = true; }
      | L.{ pl_desc = "proj"   } -> { param with proj    = true; }
      | L.{ pl_desc = "constr" } -> { param with constr  = true; }
      | L.{ pl_desc = "diffr"  } -> { param with diff    = true; }
      | L.{ pl_desc = "delta"  } -> { param with delta   = delta_full; }
      | L.{ pl_desc = "def"    } ->
        { param with delta   = { param.delta with def = true;} }
      | L.{ pl_desc = "op"     } ->
        { param with delta   = { param.delta with op = true;} }
      | L.{ pl_desc = "macro"  } ->
        { param with delta   = { param.delta with macro = true;} }
      | L.{ pl_desc = "builtin"} -> { param with builtin = true; }

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
  (** {2 Reduction state} *)

  (*------------------------------------------------------------------*)
  (** reduction state *)
  type state = { 
    table     : Symbols.table;
    params    : Params.t;
    vars      : Vars.env;         (* used to get variable tags *)
    system    : SE.context;
    red_param : red_param;
    hyps      : THyps.hyps;

    expand_context : Macros.expand_context;
    (** expantion mode for macros. See [Macros.expand_context]. *)
  }

  (*------------------------------------------------------------------*)
  (** Make a reduction state directly *)
  let mk_state
      ?(expand_context = Macros.InSequent)
      ?(hyps      = THyps.empty)
      ?(params    = Params.empty )
      ~(system    : SE.context)
      ?(vars      = Vars.empty_env)
      ~(red_param : red_param)
      (table      : Symbols.table)
    : state 
    =
    { table; system; params; red_param; hyps; expand_context; vars; }


  (*------------------------------------------------------------------*)
  (** Change the system context of a [state], updating its hypotheses
      accordingly. *)
  let change_context (st : state) (new_context : SE.context) : state =
    let hyps = 
      Hyps.change_trace_hyps_context
        ~old_context:st.system ~new_context
        ~table:st.table ~vars:st.vars st.hyps
    in
    { st with system = new_context; hyps; } 

  (*------------------------------------------------------------------*)
  let add_hyp (f : Term.term) hyps : THyps.hyps =
    THyps.add TacticsArgs.AnyName (LHyp (Local f)) hyps

  (*------------------------------------------------------------------*)
  (** {2 Conversion} *)

  (** conversion state *)
  type cstate = {
    rst   : state;              (** a reduction state *)
    subst : Term.subst;
    (** pending variable to variable substitution (left -> right) *)
  }

  let cstate_of_state (c : state) : cstate = { rst = c; subst = []; }

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
        if not (Ident.equal tv1 tv2) then not_conv ()
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
    | Term.Int i1, Term.Int i2 ->
      if not (Z.equal i1 i2) then not_conv ()

    | Term.String s1, Term.String s2 ->
      if not (String.equal s1 s2) then not_conv ()

    | Term.Fun (fs1, app_fty1), Term.Fun (fs2, app_fty2)
      when fs1 = fs2 ->
      conv_applied_ftype app_fty1 app_fty2

    | Term.Name (ns1,l1), Term.Name (ns2,l2) when ns1.s_symb = ns2.s_symb ->
      assert (Type.equal ns1.Term.s_typ ns2.Term.s_typ);
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
      assert (Type.equal ms1.Term.s_typ ms2.Term.s_typ);
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

    | Term.Var v1, Term.Var v2 ->
      begin
        try conv_var st v1 v2
        with NotConv -> conv_try_reduce st t1 t2
      end

    | Term.App (u1, v1), Term.App (u2, v2) ->
      if List.length v1 <> List.length v2 then not_conv ();
      conv_l st (u1 :: v1) (u2 :: v2)

    | Term.Tuple l1, Term.Tuple l2 ->
      if List.length l1 <> List.length l2 then not_conv ();
      conv_l st l1 l2

    | Term.Proj (i1, u1), Term.Proj (i2, u2) ->
      if i1 <> i2 then conv_try_reduce st t1 t2 else
        conv st u1 u2

    | Term.Let (v1,t1,s1), Term.Let (v2,t2,s2) ->
      let st' = conv_bnd st v1 v2 in
      conv st  t1 t2;
      conv st' s1 s2
      (* FEATURE: we could more agressively rely on reduction during
         conversion in several cases (e.g. `Let` and `App`), but this
         impact performances *)
      (* begin *)
      (*   try *)
      (*     let st' = conv_bnd st v1 v2 in *)
      (*     conv st  t1 t2; *)
      (*     conv st' s1 s2 *)
      (*   with NotConv -> conv_try_reduce st t1 t2 *)
      (* end *)
      
    | Term.Int    _, _
    | Term.String _, _
    | Term.Fun    _, _
    | Term.Name   _, _
    | Term.Action _, _
    | Term.Diff   _, _
    | Term.Macro  _, _
    | Term.Quant  _, _
    | Term.Find   _, _
    | Term.Var    _, _
    | Term.App    _, _
    | Term.Tuple  _, _
    | Term.Proj   _, _

    | _, Term.Int    _
    | _, Term.String _
    | _, Term.Fun    _
    | _, Term.Name   _
    | _, Term.Action _
    | _, Term.Diff   _
    | _, Term.Macro  _
    | _, Term.Quant  _
    | _, Term.Find   _
    | _, Term.Var    _
    | _, Term.App    _
    | _, Term.Tuple  _
    | _, Term.Proj   _ -> conv_try_reduce st t1 t2

  and conv_l (st : cstate) (ts1 : Term.terms) (ts2 : Term.terms) : unit =
    List.iter2 (conv st) ts1 ts2

  (** Reduce [t1] or [t2] and resume the convertion check.

      Let [st.subst = θ], remark that we try to reduce [t1] and not
      [t1 θ] (idem for [t2]).
      This is not an issue, since if [t1 ⇝ t1'] then [t1 θ ⇝ t1' θ]
      when [θ] is a variable renaming. *)
  and conv_try_reduce (st : cstate) (t1 : Term.t) (t2 : Term.t) : unit =
    let t1, has_red = reduce_head1_term st.rst t1 in
    if has_red then conv st t1 t2
    else
      let t2, has_red = reduce_head1_term st.rst t2 in
      if has_red then conv st t1 t2
      else not_conv ()

  (*------------------------------------------------------------------*)
  (** {2 Reduction functions} *)

  (** Internal.
      Invariant: we must ensure that fv(reduce(u)) ⊆ fv(t)
      Return: reduced term, reduction occurred *)
  (* FEATURE: memoisation? *)
  and reduce_term (st : state) (t : Term.term) : Term.term * bool = 
    let t, has_red = reduce_head1_term st t in

    if has_red then fst (reduce_term st t), true
    else
      let t, has_red = reduce_subterms ~f_red:reduce_term st t in
      if has_red then fst (reduce_term st t), true
      else t, false

  (*------------------------------------------------------------------*)
  (** Exported.
      Weak head normal form. *)
  and whnf_term
      ?(strat : red_strat = Std)
      (st : state) (t : Term.term) : Term.term * bool
    =
    (* reduce in head position as much as possible *)
    let rec doit t =
      let t, has_red = reduce_head1_term ~strat st t in
      if has_red then doit t else t
    in

    let t, has_red = reduce_head1_term ~strat st t in
    if has_red then doit t, true else t, false

  (** Auxiliary function reducing once at head position. 
      The reduction strategy is implemented in [reduce_head1_term]. *)
  and red_head1 : state -> Term.t -> Term.t * bool =
    let red_rules =
      [
        reduce_delta1    ;     (* δ *)
        rewrite_head_once;     (* user rewriting rules *)
        reduce_beta1     ;     (* β *)
        reduce_proj1     ;     (* proj *)
        reduce_diff1     ;     (* diff *)
        reduce_let1      ;     (* zeta *)
        reduce_constr1   ;     (* constr *)
        reduce_builtin   ;     (* builtin *)
      ]
    in
    let rec try_red red_funcs (st : state) (t : Term.t) : Term.t * bool =
      match red_funcs with
      | [] -> t, false
      | red_f :: red_funcs ->
        let t0, has_red = red_f st t in
        if has_red then t0, true
        else try_red red_funcs st t
    in

    fun (st : state) (t : Term.term) -> try_red red_rules st t
      
  (** Reduce once at head position.
      May use all reduction rules:
       [δ, user rewriting rules, β, proj, diff, zeta, constr] *)
  and reduce_head1_term
      ?(strat : red_strat = Std)
      (st : state) (t : Term.term) : Term.term * bool
    =
    let t, has_red = red_head1 st t in
    match strat, has_red with
    | Std, _ | MayRedSub _, true -> t, has_red
    | MayRedSub red_param, false ->
      (* put strict subterms in whnf and try to reduce at head position again *)
      let t', has_red_sub =
        reduce_subterms ~f_red:(whnf_term ~strat:Std) { st with red_param; } t
      in
      if has_red_sub then
        let t', has_red = red_head1 st t' in
        if has_red then t', true else t, false
      else t, false


  (*------------------------------------------------------------------*)
  (* β-reduction *)
  and reduce_beta1 (st : state) (t : Term.term) : Term.term * bool =
    if not st.red_param.beta then t, false
    else 
      match t with
      | Term.App (Term.Quant (Term.Lambda, v :: evs, t0), arg :: args) -> 
        let evs, subst = Term.refresh_vars evs in
        let t0 = Term.subst (Term.ESubst (Term.mk_var v, arg) :: subst) t0 in
        Term.mk_app (Term.mk_lambda evs t0) args, true

      | _ -> t, false

  (** (local) let reduction *)
  and reduce_let1 (st : state) (t : Term.term) : Term.term * bool =
    if not st.red_param.zeta then t, false
    else
      match t with
      | Term.Let (v,t1,t2) -> Term.subst [Term.ESubst (Term.mk_var v, t1)] t2, true
      | _ -> t, false

  (** projection reduction *)
  and reduce_proj1 (st : state) (t : Term.term) : Term.term * bool =
    if not st.red_param.proj then t, false
    else
      match t with
      | Term.Proj (i, Term.Tuple ts) -> List.nth ts (i - 1), true
      | _ -> t, false

  and reduce_diff1 (st : state) (t : Term.term) : Term.term * bool =
    if not st.red_param.diff || not (SE.is_fset st.system.set) then t, false
    else
      let se = SE.to_fset st.system.set in
      Term.head_normal_biterm0 (SE.to_projs se) t

  (* Try to show using [Constr] that [t] is [false] or [true] *)
  and reduce_constr1 (st : state) (t : Term.term) : Term.term * bool =
    if not st.red_param.constr ||
       Term.ty t <> Type.tboolean ||
       Term.equal t Term.mk_false ||
       Term.equal t Term.mk_true
    then t, false
    else
      let exception NoExp in
      try
        let timeout = TConfig.solver_timeout st.table in
        if Constr.(is_tautology ~exn:NoExp ~timeout ~table:st.table t )
        then Term.mk_true,true
        else if Constr.(is_tautology ~exn:NoExp ~timeout ~table:st.table (Term.mk_not t))
        then Term.mk_false,true
        else t,false   
      with NoExp -> (t,false)

  (* Expand once at head position *)
  and reduce_delta1 (st : state) (t : Term.term) : Term.term * bool = 
    Match.reduce_delta1
      ~delta:st.red_param.delta
      ~mode:st.expand_context st.table st.system st.hyps t

  and reduce_builtin (st : state) (t : Term.t) : Term.t * bool =
    if not st.red_param.builtin then t, false
    else
      let open Library.Int in
      let table = st.table in

      match Term.decompose_app t with
      (* Int.( + ) *)
      | Fun (fs,_), [Int i1; Int i2] when fs = add table ->
        Term.mk_int Z.(i1 + i2), true

      (* Int.( - ) *)
      | Fun (fs,_), [Int i1; Int i2] when fs = minus table ->
        Term.mk_int Z.(i1 - i2), true

      (* Int.( * ) *)
      | Fun (fs,_), [Int i1; Int i2] when fs = mul table ->
        Term.mk_int Z.(i1 * i2), true

      (* Int.opp *)
      | Fun (fs,_), [Int i]          when fs = opp table ->
        Term.mk_int Z.(- i), true

      | _ -> t, false

  (* Rewrite once at head position *)
  and rewrite_head_once (st : state) (t : Term.term) : Term.term * bool = 
    if not st.red_param.rewrite then t, false 
    else 
      let db = Hint.get_rewrite_db st.table in
      let hints = Term.Hm.find_dflt [] (Term.get_head t) db in

      let rule = List.find_map (fun Hint.{ cnt = rule } ->
          match 
            Rewrite.rewrite_head
              st.table st.params st.vars st.expand_context st.hyps st.system.set
              rule t 
          with
          | None -> None
          | Some (red_t, subs) ->
            let subs_valid =  
              List.for_all (fun (se, sub) -> 
                  let new_context = { st.system with set = se; } in
                  let st_sub =
                    { (change_context st new_context) with red_param = rp_default; } 
                  in
                  (* FEATURE: conversion *)
                  fst (reduce_term st_sub sub) =
                  Term.mk_true
                ) subs
            in              
            if subs_valid then Some red_t else None            
        ) hints
      in

      match rule with
      | None -> t, false
      | Some red_t -> red_t, true

  (** Reduce all strict subterms according to [f_red] *)
  and reduce_subterms
      ~(f_red : state -> Term.term -> Term.term * bool)
      (st : state) (t : Term.term)
    : Term.term * bool
    =
    match t with
    | Term.Quant (q, evs, t0) -> 
      let _, subst = Term.refresh_vars evs in
      let t0 = Term.subst subst t0 in
      let red_t0, has_red =
        let vars = Vars.add_vars (Vars.Tag.local_vars evs) st.vars in
        f_red { st with vars } t0
      in

      if not has_red then t, false
      else
        let r_subst = rev_subst subst in
        let red_t0 = Term.subst r_subst red_t0 in
        let red_t = Term.mk_quant ~simpl:false q evs red_t0 in
        red_t, true

    (* if-then-else *)
    | Term.App (Fun (fs, fty), [c;t;e]) when fs = Term.f_ite -> 
      let c, has_red0 = f_red st c in

      let hyps_t = add_hyp c st.hyps in
      let hyps_f = add_hyp (Term.mk_not ~simpl:true c) st.hyps in

      let t, has_red1 = f_red { st with hyps = hyps_t } t in
      let e, has_red2 = f_red { st with hyps = hyps_f } e in

      Term.mk_fun0 fs fty [c; t; e],
      has_red0 || has_red1 || has_red2

    (* [φ => ψ] *)
    | Term.App (Fun (fs, fty), [f1;f2]) when fs = Term.f_impl -> 
      let hyps2 = add_hyp f1 st.hyps in

      let f1, has_red1 = f_red st f1 in
      let f2, has_red2 = f_red { st with hyps = hyps2 } f2 in      

      Term.mk_fun0 fs fty [f1;f2],
      has_red1 || has_red2

    (* [φ && ψ] is handled as [φ && (φ => ψ)] *)
    | Term.App (Fun (fs, fty), [f1;f2]) when fs = Term.f_and -> 
      let hyps2 = add_hyp f1 st.hyps in

      let f1, has_red1 = f_red st f1 in
      let f2, has_red2 = f_red { st with hyps = hyps2 } f2 in      

      Term.mk_fun0 fs fty [f1;f2],
      has_red1 || has_red2

    (* [φ || ψ] is handled as [φ || (¬ φ => ψ)] *)
    | Term.App (Fun (fs, fty), [f1;f2]) when fs = Term.f_or -> 
      let hyps2 = add_hyp (Term.mk_not f1) st.hyps in

      let f1, has_red1 = f_red st f1 in
      let f2, has_red2 = f_red { st with hyps = hyps2 } f2 in      

      Term.mk_fun0 fs fty [f1;f2],
      has_red1 || has_red2

    | Term.Find (is, c, t, e) -> 
      let _, subst = Term.refresh_vars is in
      let c, t = Term.subst subst c, Term.subst subst t in
      let st1 =
        let vars = Vars.add_vars (Vars.Tag.local_vars is) st.vars in
        { st with vars }
      in

      let c, has_red0 = f_red st1 c in

      let hyps_t = add_hyp c st.hyps in
      let hyps_f =
        add_hyp (Term.mk_forall is (Term.mk_not ~simpl:true c)) st.hyps
      in

      let t, has_red1 = f_red { st1 with hyps = hyps_t } t in
      let e, has_red2 = f_red { st  with hyps = hyps_f } e in

      let r_subst = rev_subst subst in
      let c, t = Term.subst r_subst c, Term.subst r_subst t in

      Term.mk_find ~simpl:true is c t e,
      has_red0 || has_red1 || has_red2

    | Term.Diff (Explicit l) -> 
      let has_red, l = 
        List.map_fold (fun has_red (label,t) -> 
            let new_context = 
              { st.system with set = SE.project [label] st.system.set; }
            in
            let st = change_context st new_context in
            let t, has_red' = f_red st t in
            has_red || has_red', (label, t)
          ) false l
      in
      Term.mk_diff l, has_red

    | Term.Int    _
    | Term.String _
    | Term.Let    _
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
            let t, has_red' = f_red st t in
            has_red || has_red', t
          ) false t
      in
      t, has_red

  (*------------------------------------------------------------------*)
  (** {2 Global formula reduction} *)

  (*------------------------------------------------------------------*)
  let reduce_glob_let1 (st : state) (t : Equiv.form) : Equiv.form * bool =
    if not st.red_param.zeta then t, false
    else Match.reduce_glob_let1 t

  (*------------------------------------------------------------------*)
  (** Reduce once at head position in a global formula.
      May use all reduction rules:
       [zeta ] *)
  let reduce_head1_global (st : state) (t : Equiv.form) : Equiv.form * bool = 
    let rec try_red red_funcs =
      match red_funcs with
      | [] -> t, false
      | red_f :: red_funcs ->
        let t, has_red = red_f t in
        if has_red then t, true
        else try_red red_funcs
    in
    try_red [reduce_glob_let1 st; ]     (* zeta *)

  (*------------------------------------------------------------------*)
  (** {2 Global formula convertion} *)
  
  let rec conv_g (st : cstate) (e1 : Equiv.form) (e2 : Equiv.form) : unit =
    match e1, e2 with
    | Equiv.Quant (q1, vs1, e1), Equiv.Quant (q2, vs2, e2) when q1 = q2 ->
      if List.length vs1 <> List.length vs2 then not_conv ();
      let st = conv_tagged_bnds st vs1 vs2 in
      conv_g st e1 e2

    | Equiv.And  (el1, er1), Equiv.And  (el2, er2)
    | Equiv.Or   (el1, er1), Equiv.Or   (el2, er2)
    | Equiv.Impl (el1, er1), Equiv.Impl (el2, er2)->
      conv_g_l st [el1; er1] [el2; er2]

    | Equiv.Atom (Pred p1), Equiv.Atom (Pred p2) when p1.psymb = p2.psymb ->
      conv_tys p1.ty_args p2.ty_args;
      conv_systems st.rst.table p1.se_args p2.se_args;

      List.iter2 (fun (se1,l1) (se2,l2) ->
          assert (SE.equal st.rst.table se1 se2);
          let system = SE.{set = (se1 :> SE.t); pair = None; } in
          conv_l { st with rst = { st.rst with system} } l1 l2
        ) p1.multi_args p2.multi_args;

      let system = SE.{set = (SE.of_list [] :> SE.t); pair = None; } in
      conv_l { st with rst = { st.rst with system} } p1.simpl_args p2.simpl_args

    | Equiv.Atom (Reach f1), Equiv.Atom (Reach f2) ->
      let system = SE.{set = st.rst.system.set; pair = None; } in
      conv { st with rst = { st.rst with system} } f1.formula f2.formula

    | Equiv.Atom (Equiv ts1), Equiv.Atom (Equiv ts2) ->
      let system =
        SE.{set = (oget st.rst.system.pair :> SE.arbitrary); pair = None; }
      in
      conv_l { st with rst = { st.rst with system} } ts1.terms ts2.terms

    | Equiv.Let (v1,t1,f1), Equiv.Let (v2,t2,f2) ->
      let st' = conv_bnd st v1 v2 in
      conv   st  t1 t2;
      conv_g st' f1 f2

    (* FEATURE: reduce head when conversion fails *)
    | Equiv.Atom (Pred _ | Reach _ | Equiv _), _
    | Equiv.Quant _, _
    | Equiv.Impl  _, _
    | Equiv.Or    _, _
    | Equiv.And   _, _
    | Equiv.Let   _, _ ->
      not_conv ()

  and conv_g_l
      (st : cstate) (es1 : Equiv.form list) (es2 : Equiv.form list) : unit
    =
    List.iter2 (conv_g st) es1 es2

  (*------------------------------------------------------------------*)
  (** {2 Exported reduction and convertion fonctions} *)

  (*------------------------------------------------------------------*)
  (** Exported. *)
  let reduce_term (st : state) (t : Term.term) : Term.term = fst (reduce_term st t)

  (*------------------------------------------------------------------*)
  (** Exported *)
  let conv (s : state) (t1 : Term.term) (t2 : Term.term) : bool =
    let s = cstate_of_state s in
    try conv s t1 t2; true with NotConv -> false

  (** Exported *)
  let conv_g (s : state) (t1 : Equiv.form) (t2 : Equiv.form) : bool =
    let s = cstate_of_state s in
    try conv_g s t1 t2; true with NotConv -> false

  (*------------------------------------------------------------------*)
end (* Core *)

(*------------------------------------------------------------------*)
(** {2 Register [Core] in [ReductionCore]} *)

let () = ReductionCore.Register.store (module Core)

include Core

(*------------------------------------------------------------------*)
(** {2 Reduction functions from a sequent} *)

(*------------------------------------------------------------------*)
module type S = sig
  type t                        (* type of sequent *)

  (*------------------------------------------------------------------*)
  val to_state :
    ?expand_context:Macros.expand_context  ->
    ?system:SE.context ->
    ?vars:Vars.env ->
    red_param -> t -> state

  (*------------------------------------------------------------------*)
  val reduce_global : 
    ?expand_context:Macros.expand_context ->
    ?system:SE.context -> 
    red_param -> t -> Equiv.form -> Equiv.form

  val reduce : 
    ?expand_context:Macros.expand_context ->
    ?system:SE.context -> 
    red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a

  (** reduces once at head position *)
  val reduce_head1 :
    ?expand_context:Macros.expand_context ->
    ?system:SE.context -> 
    red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a * bool

  (*------------------------------------------------------------------*)
  (** {2 expantion and destruction modulo } *)

  val destr_eq : 
    t -> 'a Equiv.f_kind -> 'a -> (Term.term * Term.term) option

  val destr_not : 
    t -> 'a Equiv.f_kind -> 'a -> Term.term option

  val destr_or : 
    t -> 'a Equiv.f_kind -> 'a -> ('a * 'a) option

  val destr_and : 
    t -> mode:SmartFO.mode -> 'a Equiv.f_kind -> 'a -> ('a * 'a) option

  (*------------------------------------------------------------------*)
  (** {2 conversion from a sequent } *)

  val conv_term :
    ?expand_context:Macros.expand_context -> 
    ?system:SE.context -> 
    ?param:red_param ->
    t ->
    Term.term -> Term.term -> bool

  val conv_global : 
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

module Mk (S : LowSequent.S) : S with type t := S.t = struct

  (*------------------------------------------------------------------*)
  (** Build a reduction state from a sequent. 
      [system] is the system of the term being reduced. *)
  let to_state
      ?(expand_context : Macros.expand_context = InSequent) 
      ?(system   : SE.context option)
      ?(vars     : Vars.env option) (* overloads [s] variables *)
      (red_param : red_param)
      (s         : S.t)
    : state
    = 
    let table = S.table s in
    let vars  = odflt (S.vars s) vars in

    let old_context = S.system s in
    let new_context = odflt old_context system in
    let hyps = S.get_trace_hyps s in
    let hyps = 
      Hyps.change_trace_hyps_context
        ~old_context ~new_context
        ~table ~vars:(S.vars s)
        hyps
    in

    { table;
      params = S.params s;
      system = new_context;
      vars;
      red_param;
      hyps;
      expand_context; } 

  (*------------------------------------------------------------------*)
  (** Exported.
      We need type introspection here. *)
  let reduce_head1 (type a) 
      ?(expand_context : Macros.expand_context option)
      ?(system : SE.context option)
      (param : red_param) (s : S.t)
      (k : a Equiv.f_kind) (x : a) : a * bool
    =
    let st = to_state ?expand_context ?system param s in
    match k with
    | Local_t  -> reduce_head1_term   st x
    | Global_t -> reduce_head1_global st x
    | Any_t ->
      match x with
      | Local  x -> 
        let x, has_red = reduce_head1_term st x in
        Local x, has_red

      | Global x -> 
        let x, has_red = reduce_head1_global st x in
        Global x, has_red

  (*------------------------------------------------------------------*)
  (** Exported. *)
  let reduce_global
      ?(expand_context : Macros.expand_context option)
      ?(system : SE.context option)
      (param : red_param) (s : S.t) (e : Equiv.form) 
    : Equiv.form 
    =
    let system = odflt (S.system s) system in
    let env = { (S.env s) with system; } in

    let rec reduce_g (vars : Vars.env) (e : Equiv.form) : Equiv.form =
      match e with
      | Equiv.Quant (q, vs, e) -> 
        let _, subst = Term.refresh_vars_w_info vs in
        let e = Equiv.subst subst e in
        let red_e =
          let vars = Vars.add_vars vs vars in
          reduce_g vars e
        in

        let r_subst = rev_subst subst in
        let red_e = Equiv.subst r_subst red_e in
        Equiv.Quant (q, vs, red_e)

      | Equiv.Let (v,t,f) ->
        if param.zeta then
          let e, _ = Match.reduce_glob_let1 e in
          reduce_g vars e
        else
          begin
            (* reduce [f] *)
            let vtag = v, HighTerm.tags_of_term env t in
            let _, subst = Term.refresh_vars_w_info [vtag] in
            let f = Equiv.subst subst f in
            let f =
              let vars = Vars.add_vars [vtag] vars in
              reduce_g vars f
            in

            let r_subst = rev_subst subst in
            let f = Equiv.subst r_subst f in

            (* reduce [t], which is w.r.t. [pair] *)
            let system = { system with set = (oget system.pair :> SE.t); } in
            let state = to_state ?expand_context ~system ~vars param s in
            let t = reduce_term state t in

            Equiv.Let (v,t,f)
          end

      | Equiv.And (e1, e2) ->
        Equiv.And (reduce_g vars e1, reduce_g vars e2)

      | Equiv.Or (e1, e2) ->
        Equiv.Or (reduce_g vars e1, reduce_g vars e2)

      | Equiv.Impl (e1, e2) ->
        Equiv.Impl (reduce_g vars e1, reduce_g vars e2)

      | Equiv.Atom (Reach f) ->
        let state = to_state ?expand_context ~system ~vars param s in
        let f = reduce_term state f.formula in
        Equiv.Atom (Reach {formula =f; bound = None})
       (*TODO:Concrete : Probably something to do to create a bounded goal*)

      | Equiv.Atom (Equiv e) ->
        let system = { system with set = (oget system.pair :> SE.t); } in
        let state = to_state ?expand_context ~system ~vars param s in

        let e = List.map (reduce_term state) e.terms in
        Equiv.Atom (Equiv.Equiv {terms = e; bound = None})
       (*TODO:Concrete : Probably something to do with the reduction of the bound*)

      | Equiv.Atom (Pred pa) ->
        let simpl_args =
          let system = { system with set = (SE.of_list [] :> SE.t); } in
          let state = to_state ?expand_context ~system ~vars param s in
          List.map (reduce_term state) pa.simpl_args
        in
        let multi_args =
          List.map (fun (se,args) ->
              let system = { system with set = se; } in
              let state = to_state ?expand_context ~system ~vars param s in
              ( se, List.map (reduce_term state) args )
            ) pa.multi_args
        in
        Equiv.Atom (Equiv.Pred { pa with simpl_args; multi_args; })
    in
    reduce_g (S.vars s) e

  (** We need type introspection there *)
  let reduce (type a) 
      ?(expand_context : Macros.expand_context option)
      ?(system : SE.context option)
      (param : red_param)
      (s : S.t) (k : a Equiv.f_kind) (x : a) : a 
    =
    let st = to_state ?expand_context ?system param s in
    match k with
    | Local_t  -> reduce_term st x
    | Global_t -> reduce_global ?expand_context ?system param s x
    | Any_t ->
      match x with
      | Local  x -> Local  (reduce_term st x)
      | Global x -> Global (reduce_global ?expand_context ?system param s x)

  (*------------------------------------------------------------------*)
  (** Destruct [x] according to an arbitrary destruct function [destr_f], 
      using [s] to reduce [x] if necessary. *)
  let mk_destr (type a)
      (destr_f : Term.term -> 'b option)
      (s : S.t) (k : a Equiv.f_kind)
      (x : a) : 'b option
    =
    let rec destr_term (x : Term.term) =
      match destr_f x with
      | Some _ as res -> res
      | None ->
        let x, has_red = reduce_head1_term (to_state rp_full s) x in
        if not has_red then 
          None                  (* did not reduce, failed *)
        else
          destr_term x          (* reduced, recurse to try again *)
    in
    match k with
    | Local_t  -> destr_term  x
    | Global_t -> None
    | Any_t ->
      match x with
      | Local  x -> destr_term  x
      | Global _ -> None

  (*------------------------------------------------------------------*)
  (** Similar to [mk_destr], but with a dependent return type and
      two different destruct functions. *)
  let mk_destr_k (type a)
      (destr_t0 : Term.term  -> (Term.term  * Term.term ) option)
      (destr_e0 : Equiv.form -> (Equiv.form * Equiv.form) option)
      (s : S.t) (k : a Equiv.f_kind)
      (x : a) : (a * a) option
    =
    let rec destr_t (x : Term.term) =
      match destr_t0 x with
      | Some _ as res -> res
      | None ->
        let x, has_red = reduce_head1_term (to_state rp_full s) x in
        if not has_red then 
          None               (* did not reduce, failed *)
        else
          destr_t x          (* reduced, recurse to try again *)
    in
    let rec destr_e (x : Equiv.form) =
      match destr_e0 x with
      | Some _ as res -> res
      | None ->
        let x, has_red = reduce_head1_global (to_state rp_full s) x in
        if not has_red then 
          None               (* did not reduce, failed *)
        else
          destr_e x          (* reduced, recurse to try again *)
    in

    match k with
    | Local_t  -> destr_t x
    | Global_t -> destr_e x
    | Any_t ->
      match x with
      | Local  x -> omap (fun (a,b) -> Equiv.Local  a, Equiv.Local  b) (destr_t x)
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
      (s : S.t) ~(mode : SmartFO.mode) (k : a Equiv.f_kind)
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
    mk_destr_k destr_and (Equiv.Smart.destr_and ~mode ~env:(S.env s)) s k x

  (*------------------------------------------------------------------*)
  (** Exported. *)
  let conv_term
      ?(expand_context : Macros.expand_context option)
      ?(system : SE.context option)
      ?(param : red_param = rp_default)
      (s : S.t)
      (t1 : Term.term) (t2 : Term.term) : bool
    =
    let state = to_state ?expand_context ?system param s in
    conv state t1 t2

  (** Exported. *)
  let conv_global
      ?(expand_context : Macros.expand_context option)
      ?(system : SE.context option)
      ?(param : red_param = rp_default)
      (s : S.t)
      (e1 : Equiv.form) (e2 : Equiv.form) : bool
    =
    let state = to_state ?expand_context ?system param s in
    conv_g state e1 e2

  (** We need type introspection there *)
  let conv_kind (type a) 
      ?(expand_context : Macros.expand_context = InSequent)
      ?(system : SE.context option)
      ?(param : red_param = rp_default)
      (s : S.t) (k : a Equiv.f_kind)
      (x1 : a) (x2 : a) : bool
    =
    match k with
    | Local_t  -> conv_term   ~expand_context ?system ~param s x1 x2
    | Global_t -> conv_global ~expand_context ?system ~param s x1 x2
    | Any_t ->
      match x1, x2 with
      | Local  x1, Local  x2 -> conv_term   ~expand_context ?system ~param s x1 x2
      | Global x1, Global x2 -> conv_global ~expand_context ?system ~param s x1 x2
      | _, _ -> false

end

