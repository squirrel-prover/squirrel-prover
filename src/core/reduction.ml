open Utils

module L = Location

include ReductionCore

(*------------------------------------------------------------------*)
let rev_subst subst = 
  List.map (fun (Term.ESubst (u,v)) -> Term.ESubst (v,u)) subst

(*------------------------------------------------------------------*)
(** {2 Core reduction functions} *)

(** reduction state *)
type reduction_state = {
  pc        : ProofContext.t;
  red_param : red_param;
}

(*------------------------------------------------------------------*)
let set_concrete
    (concrete:bool) (state : reduction_state) 
  : reduction_state 
  =
	{ state with pc = ProofContext.set_concrete concrete state.pc } 

module Core : (ReductionCore.Sig with type state = reduction_state) = struct

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
  type state = reduction_state

  (*------------------------------------------------------------------*)
  (** Make a reduction state directly *)
  let mk_state0
      ?(hyps      = THyps.empty)
      ?(params    = Params.empty )
      ~(system    : SE.context)
      ?(vars      = Vars.empty_env)
      ~(concrete  : bool)
      ~(red_param : red_param)
      (table      : Symbols.table)
    : state 
    =
    let env =
      Env.init ~table ~system
        ~ty_vars:params.ty_vars ~se_vars:params.se_vars ~vars ()
    in
    let pc = ProofContext.make ~env ~hyps ~concrete in
    { pc; red_param; }

  (*------------------------------------------------------------------*)
  let mk_state (pc : ProofContext.t) ~red_param : state = { pc; red_param; }

  (*------------------------------------------------------------------*)
  (** Change the system context of a [state], updating its hypotheses
      accordingly. *)
  let change_context (new_context : SE.context) (st : state) : state =
    { st with pc = ProofContext.change_system ~system:new_context st.pc }

  (*------------------------------------------------------------------*)
  let add_vars (vars : Vars.tagged_vars) (st : state) : state =
    let vars = Vars.add_vars vars st.pc.env.vars in
    { st with pc = ProofContext.set_vars vars st.pc; }
    
  (*------------------------------------------------------------------*)
  let add_hyp (f : Term.term) (st : state) : state =
    let hyps = THyps.add TacticsArgs.AnyName (LHyp (Local f)) st.pc.hyps in
    { st with pc = ProofContext.set_hyps hyps st.pc; }

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
  (* Those functions are the concrete function for the advantage of
     cryptographic hypothesis, this allows us to create for special
     cases for them, see the case for more detail *)
    let adv_crypto_funs table =
      if Library.Concrete.is_loaded table
      then
        [Library.Concrete.fs_adv_intctxt table]
      else
        []

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

    (* Special case for the cryptographic time function, those
       functions take reification of some term, and inside those
       functions, we want to consider the reification up to
       alpha-renaming of variables *)
    (*FEAT:Concrete: Add a similar rule in unification*)
    | Term.App(Term.Fun(f1,_),v1), Term.App(Term.Fun(f2,_),v2)
        when Symbols.path_equal f1 f2 && 
             List.mem_cmp ~eq:Symbols.path_equal
               f1 (adv_crypto_funs st.rst.pc.env.table)
             && List.length v1 = List.length v2 ->
        (* This function check the convertibility of the reification
           of two terms upto alpha renaming only *)
        let eq_quote t1 t2 =
          let env = st.rst.pc.env in
          (* Here, we use rp_empty to only allow alpha renaming inside
             the recurisve call on the reification *)
          let new_st = {st with rst = {st.rst with red_param = rp_empty}} in
          (* Those two functions allows us to compute the unquoting of
             the reification with the detail that some of them are
             optional *)
          let unquote t =
            match Reify.unquote env t with
            | None -> `ReifyFailed
            | Some t1 -> `ReifySuccess t1
          in
          let ounquote t =
            match  t with
              | Term.App((Fun(f, _ )),[t])
                when Symbols.path_equal f (Library.Concrete.ReifyOption.fs_some st.rst.pc.env.table) ->
                unquote t
              | Term.Fun(f,_)
                when Symbols.path_equal f (Library.Concrete.ReifyOption.fs_none st.rst.pc.env.table) ->
                `None
              | _ -> unquote t
          in
          (* When we unquote the arguments of the functions, and try
             to convert them upto alpha renaming only (since we want
             to have the same execution time for both) *)
          match ounquote t1, ounquote t2 with
          | `ReifySuccess t1, `ReifySuccess t2 ->
            conv new_st t1 t2
          | `None, `None -> ()
          | _ -> not_conv ()
        in
        List.iter2 eq_quote v1 v2

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

  and conv_opt (st : cstate) (t1 : Term.term option) (t2 : Term.term option) : unit =
    match t1, t2 with
    | None, None -> ()
    | Some t1, Some t2 -> conv st t1 t2
    | _ -> not_conv ()

  (** Reduce [t1] or [t2] and resume the convertion check.

      Let [st.subst = θ], remark that we try to reduce [t1] and not
      [t1 θ] (idem for [t2]).
      This is not an issue, since if [t1 ⇝ t1'] then [t1 θ ⇝ t1' θ]
      when [θ] is a variable renaming. *)
  and conv_try_reduce (st : cstate) (t1 : Term.t) (t2 : Term.t) : unit =
    let t1, has_red = reduce_head1_term st.rst t1 in
    if has_red = True then conv st t1 t2
    else
      let t2, has_red = reduce_head1_term st.rst t2 in
      if has_red = True then conv st t1 t2
      else not_conv ()

  (*------------------------------------------------------------------*)
  (** {2 Reduction functions} *)

  (** Internal.
      Invariant: we must ensure that fv(reduce(u)) ⊆ fv(t)
      Return: reduced term, reduction occurred *)
  (* FEATURE: memoisation? *)
  and reduce_term (st : state) (t : Term.term) : Term.term * bool = 
    let t, has_red = reduce_head1_term st t in

    if has_red = True then fst (reduce_term st t), true
    else
      let t, has_red = reduce_subterms ~f_red:reduce_term st t in
      if has_red then fst (reduce_term st t), true
      else t, has_red

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
      if has_red = True then doit t else t
    in

    let t, has_red = reduce_head1_term ~strat st t in
    if has_red = True then doit t, true else t, false

  (** Auxiliary function reducing once at head position. 
      The reduction strategy is implemented in [reduce_head1_term]. *)
  and red_head1 : state -> Term.t -> Term.t * head_has_red =
    let red_rules =
      [
        reduce_delta1            ;     (* δ *)
        rewrite_head1            ;     (* user rewriting rules *)
        reduce_beta1             ;     (* β *)
        reduce_proj1             ;     (* proj *)
        reduce_diff1             ;     (* diff *)
        reduce_let1              ;     (* zeta *)
        reduce_constr1           ;     (* constr *)
        reduce_builtin1          ;     (* builtin *)
      ]
    in
    (* [has_red] is needed to know if one of the tried reduction rule
       needs to reduce a subterm *)
    let rec try_red
        red_funcs ~(has_red : head_has_red)
        (st : state) (t : Term.t) : Term.t * head_has_red
      =
      match red_funcs with
      | [] -> t, has_red
      | red_f :: red_funcs ->
        let t0, has_red0 = red_f st t in
        if has_red0 = True then t0, True
        else
          let has_red = has_red ||| has_red0 in
          try_red red_funcs ~has_red st t
    in

    fun (st : state) (t : Term.term) -> try_red red_rules ~has_red:False st t
      
  (** Reduce once at head position.
      May use all reduction rules:
       [δ, user rewriting rules, β, proj, diff, zeta, constr] *)
  and reduce_head1_term
      ?(strat : red_strat = Std)
      (st : state) (t : Term.term) : Term.term * head_has_red
    =
    let t, has_red = red_head1 st t in
    match strat, has_red with
    | Std, _ -> t, has_red

    | MayRedSub _, True  -> t, True
    | MayRedSub _, False -> t, False

    | MayRedSub red_param, NeedSub ->
      (* put strict subterms in whnf and try to reduce at head position again *)
      let t', has_red_sub =
        reduce_subterms ~f_red:(whnf_term ~strat:Std) { st with red_param; } t
      in
      if has_red_sub then
        let t', has_red = red_head1 st t' in
        if has_red = True then t', True else t, False
      else t, False


  (*------------------------------------------------------------------*)
  (** β-reduction 
      (error 0 reduction rule) *)
  and reduce_beta1 (st : state) (t : Term.term) : Term.term * head_has_red =
    if not st.red_param.beta then t, False
    else 
      match t with
      | Term.App (Term.Quant (Term.Lambda, v :: evs, t0), arg :: args) -> 
        let evs, subst = Term.refresh_vars evs in
        let t0 = Term.subst (Term.ESubst (Term.mk_var v, arg) :: subst) t0 in
        Term.mk_app (Term.mk_lambda evs t0) args, True

      | Term.App (_, _) -> t, NeedSub
      | _ -> t, False

  (** (local) let reduction 
      (error 0 reduction rule) *)
  and reduce_let1 (st : state) (t : Term.term) : Term.term * head_has_red =
    if not st.red_param.zeta then t, False
    else
      match t with
      | Term.Let (v,t1,t2) -> Term.subst [Term.ESubst (Term.mk_var v, t1)] t2, True
      | _ -> t, False

  (** projection reduction
      (error 0 reduction rule) *)
  and reduce_proj1 (st : state) (t : Term.term) : Term.term * head_has_red =
    if not st.red_param.proj then t, False
    else
      match t with
      | Term.Proj (i, Term.Tuple ts) -> List.nth ts (i - 1), True
      | Term.Proj (_, _) -> t, NeedSub
      | _ -> t, False

  (* error 0 reduction *)
  and reduce_diff1 (st : state) (t : Term.term) : Term.term * head_has_red =
    if not st.red_param.diff || not (SE.is_fset st.pc.env.system.set) then t, False
    else
      let se = SE.to_fset st.pc.env.system.set in
      let t, has_red = Term.head_normal_biterm0 (SE.to_projs se) t in
      if has_red then t, True else
        match t with
        | Term.Diff _ -> t, NeedSub
        | _           -> t, False

  (** try to show using [Constr] that [t] is [false] or [true] *)
  and reduce_constr1 (st : state) (t : Term.term) : Term.term * head_has_red =
    if not st.red_param.constr ||
       Term.ty t <> Type.tboolean ||
       Term.equal t Term.mk_false ||
       Term.equal t Term.mk_true
    then t, False
    else
      let exception NoExp in
      try
        let pc = st.pc in
        let timeout = TConfig.solver_timeout pc.env.table in
        let red_fun = fun x -> fst(reduce_term st x) in
        let concrete = pc.concrete in
        let models =
          Hyps.get_models ~concrete ~red_fun ~exn:NoExp ~timeout pc.env.table pc.hyps
        in
        if Constr.empty_models models then
          t, False
        else
        if Constr.query ~precise:true models [t]
        then Term.mk_true, True
        else if Constr.query ~precise:true models [Term.mk_not t]
        then Term.mk_false, True
        else t, False
      with NoExp -> t, False

  (** expand once at head position *)
  and reduce_delta1 (st : state) (t : Term.term) : Term.term * head_has_red =
    Match.reduce_delta1
      ~constr:st.red_param.constr
      ~delta:st.red_param.delta
      st.pc t

  (* error 0 reduction *)
  and reduce_builtin1 (st : state) (t : Term.t) : Term.t * head_has_red =
    let reduce_int t =
      let table = st.pc.env.table in
      if not (Library.Int.is_loaded table) then t, False
      else
        let open Library.Int in
        match Term.decompose_app t with
        (* Int.( + ) *)
        | Fun (fs,_), [Int i1; Int i2] when fs = add table ->
          Term.mk_int Z.(i1 + i2), True

        (* Int.( i + 0 = i) *)
        | Fun (fs,_), [i; Int i0] when fs = add table && Z.equal i0 Z.zero ->
          i, True

        (* Int.( 0 + i = i) *)
        | Fun (fs,_), [Int i0; i] when fs = add table && Z.equal i0 Z.zero ->
          i, True

        (* Int.( - ) *)
        | Fun (fs,_), [Int i1; Int i2] when fs = minus table ->
          Term.mk_int Z.(i1 - i2), True

        (* Int.( i - 0 = i) *)
        | Fun (fs,_), [i; Int i0] when fs = minus table && Z.equal i0 Z.zero ->
          i, True

        (* Int.( 0 - i = -i) *)
        | Fun (fs,_), [Int i0; i] when fs = minus table && Z.equal i0 Z.zero ->
          mk_opp table i, True

        (* Int.( * ) *)
        | Fun (fs,_), [Int i1; Int i2] when fs = mul table ->
          Term.mk_int Z.(i1 * i2), True

        (* Int.( i * 1 = i) *)
        | Fun (fs,_), [i; Int i1] when fs = mul table && Z.equal i1 (Z.of_int 1) ->
          i, True

        (* Int.( 1 * i = i) *)
        | Fun (fs,_), [Int i1; i] when fs = mul table && Z.equal i1 (Z.of_int 1) ->
          i, True

        (* Int.opp *)
        | Fun (fs,_), [Int i] when fs = opp table ->
          Term.mk_int Z.(- i), True

        (* Int.( = ) *)
        | Fun (fs,_), [Int i1; Int i2] when fs = Symbols.fs_eq ->
          (if Z.equal i1 i2 then Term.mk_true else Term.mk_false), True

        (* Int.( <> ) *)
        | Fun (fs,_), [Int i1; Int i2] when fs = Symbols.fs_neq ->
          (if not (Z.equal i1 i2) then Term.mk_true else Term.mk_false), True

        (* Int.( < ) *)
        | Fun (fs,_), [Int i1; Int i2] when fs = Symbols.fs_gt ->
          (if Z.gt i1 i2 then Term.mk_true else Term.mk_false), True

        (* Int.( <= ) *)
        | Fun (fs,_), [Int i1; Int i2] when fs = Symbols.fs_geq ->
          (if Z.geq i1 i2 then Term.mk_true else Term.mk_false), True

        (* Int.( > ) *)
        | Fun (fs,_), [Int i1; Int i2] when fs = Symbols.fs_lt ->
          (if Z.lt i1 i2 then Term.mk_true else Term.mk_false), True

        (* Int.( >= ) *)
        | Fun (fs,_), [Int i1; Int i2] when fs = Symbols.fs_leq ->
          (if Z.leq i1 i2 then Term.mk_true else Term.mk_false), True

        | _ -> t, NeedSub  (* FIXME: be more precise? *)
    in

    let reduce_real t =
      let table = st.pc.env.table in
      if not (Library.Real.is_loaded table) then t, False
      else
        let open Real in
        let zero = mk_zero table in
        let one = of_int table 1 in
        let cst = cstate_of_state st in
        let conv r1 r2 = try conv cst r1 r2; true with NotConv -> false in
        let (=~) = Symbols.path_equal in
        match Term.decompose_app t with
        (*1^-1 -> 1*)
        | Fun(f,_), [r]
          when f =~ fs_inv table && is_one table r -> (r, True)

        (* - - a -> a *)
        | Fun(f1,_), [App(Fun(f2,_),[r])]
          when f1 =~ fs_opp table && f2 =~ fs_opp table -> (r, True)

        (*(a)^-1^-1 -> a (if a <> 0)*)
        | Fun(f1,_), [App(Fun(f2,_),[r])]
          when f1 =~ fs_inv table && f2 =~ fs_inv table && not_is_zero table r ->  (r, True)

        (* Rule for (≤) *)
        | Fun(f,{ ty_args = [ty] }),[r1;r2] 
          when Symbols.path_equal f Library.Prelude.fs_leq &&
               Type.equal ty treal && Term.equal r1 r2 ->
          (Term.mk_true, True)

        (* Rules for unary negation (- x) *)
        | Fun(f,_), [r] when f =~ fs_opp table && is_zero table r -> (r, True)
        | Fun(f,_), [App (Fun (f',_), [Int i])] 
          when f =~ fs_opp table && f' =~ fs_of_int && Library.Int.is_loaded table -> 
          (mk_of_int table (Term.mk_int (Z.neg i)), True)

        (* Rule for (+) *)
        | Fun(f,_),[r1;r2] when f =~ fs_add table ->
          begin
            match r1, r2 with
            (* 0 + a -> a *)
            | _ when is_zero table r1 -> (r2, True)

            (* a + 0 -> a *)
            | _ when is_zero table r2 -> (r1, True)

            (* -a + a -> 0 *)
            | _ when conv r2 (mk_opp table r1) -> (zero, True)

            (* a + -a -> 0 *)
            | _ when conv r1 (mk_opp table r2) -> (zero, True)
            | _ ->
              begin
                (* we try to decompose r1 or r2 *)
                match Term.decompose_app r1, Term.decompose_app r2 with

                (*int a + int b -> int (a+b)*)
                | (Fun(f1,_),[a]) , (Fun(f2,_),[b])
                  when f1 =~ f2 && f1 =~ fs_of_int && (Library.Int.is_loaded table) ->
                  let add_int = Library.Int.mk_add table a b in
                  (mk_of_int table add_int, True)

                (* -a + -b -> -(a+b) *)
                | (Fun(f1,_),[a]), (Fun(f2,_),[b]) 
                  when f1 =~ fs_opp table && f2 =~ fs_opp table ->
                  (mk_opp table (mk_add table a b), True)

                (*-a + b -> b - a*)
                | (Fun(f1,_),[a]), _ when f1 =~ fs_opp table -> 
                  (mk_minus table r2 a, True) 

                (* a + - b -> a - b *)
                | _, (Fun(f1,_),[a]) when f1 =~ fs_opp table -> 
                  (mk_minus table r1 a, True)  

                | _ -> t, NeedSub
              end
          end

        (* Rule for (-) *)
        | Fun(f,_),[r1;r2] when f =~ fs_minus table ->
          begin
            match r1,r2 with
            (* 0 - a -> - a *)
            | _ when is_zero table r1 -> mk_opp table r2, True

            (*a - 0 -> a*)
            | _ when is_zero table r2 -> r1, True

            (* a - a -> 0 *)
            | _ when conv r1 r2 ->  zero, True
            | _ ->
              begin
                (* we try to decompose r1 or r2 *)
                match Term.decompose_app r1, Term.decompose_app r2 with

                (* int a - int b -> int (a - b) *)
                | (Fun(f1,_),[a]) , (Fun(f2,_),[b])
                  when f1 =~ f2 && f1 =~ fs_of_int && Library.Int.is_loaded table ->
                  let minus_int = Library.Int.mk_minus table a b in
                  mk_of_int table minus_int, True

                (*a - (-b) -> a + b*)
                | _, (Fun(f2,_),[b]) when f2 =~ fs_opp table -> 
                  (mk_add table r1 b, True)

                (*-a -b -> -(a+b)*)
                | (Fun(f1,_),[a]), _ when f1 =~ fs_opp table ->
                  (mk_opp table (mk_add table a r2), True)

                | _ -> t, NeedSub
              end
          end

        (* Rules for ( * ) *)
        | Fun(f,_),[r1;r2] when f = fs_mul table ->
          begin
            match r1, r2 with
            (* 0 * a -> 0 *)
            | _ when is_zero table r1 -> zero, True

            (* a * 0 -> 0 *)
            | _ when is_zero table r2 -> zero, True

            (* 1 * a -> a *)
            | _ when is_one table r1 -> r2, True

            (* a * 1 -> a *)
            | _ when is_one table r2 -> r1, True 

            (* a^-1 * a -> 1 (if a <> 0) *)
            | _ when conv r2 (mk_inv table r1) && not_is_zero table r1 -> one, True

            (* a * a^-1 -> 1 (if a <> 0) *) 
            | _ when conv r1 (mk_inv table r2) && not_is_zero table r2 -> one, True
            | _ ->
              begin
                (* we try to decompose r1 or r2 *)
                match Term.decompose_app r1, Term.decompose_app r2 with
                (* int a * int b -> int(a*b) *)
                | (Fun(f1,_),[a]) , (Fun(f2,_),[b])
                  when f1 =~ f2 && f1 =~ fs_of_int && Library.Int.is_loaded table ->
                  let mul_int = Library.Int.mk_mul table a b in
                  mk_of_int table mul_int, True

                (* a * b^-1 -> a/b *)
                | _, (Fun(f2,_),[b]) when f2 =~ fs_inv table -> 
                  (mk_div table r1 b, True)

                (* a^-1 *b -> b/a *)
                | (Fun(f1,_),[a]), _ when f1 =~ fs_inv table -> 
                  (mk_div table r2 a, True)

                (* a^-1 * b^-1 -> (a*b)^-1 *)
                | (Fun(f1, _),[a]),(Fun(f2,_),[b]) 
                  when f1 =~ fs_inv table  && f2 =~ fs_inv table ->
                  mk_inv table (mk_mul table a b), True

                (* b * a/b -> a (if b <> 0)*)
                | _,(Fun(f,_),[a;b])
                  when f =~ fs_div table && conv b r1 && not_is_zero table b ->  a, True

                (* a/b * b -> a (if b <> 0) *)
                | (Fun(f,_),[a;b]),_ 
                  when f =~ fs_div table && conv b r2 && not_is_zero table b -> 
                  a, True

                | _ -> t, NeedSub
              end
          end

        (* rule on / *)
        | Fun(f,_),[r1;r2] when f =~ fs_div table ->
          begin
            match r1, r2 with
            (* 0 / a -> 0 (if a <> 0) *)
            | _ when is_zero table r1 && not_is_zero table r2 -> zero, True

            (* a / 1 -> a *)
            | _ when is_one table r2 -> r1, True
            | _ ->
              (* We decompose r1, r2 *)
              match Term.decompose_app r1, Term.decompose_app r2 with

              (* a / b^-1 -> a * b *)
              | _, (Fun(f2,_),[b]) when f2 =~ fs_inv table && not_is_zero table b ->
                (mk_mul table r1 b),True

              (* a^-1 / b -> (a * b)^-1 *)
              | (Fun(f1,_),[a]), _ when f1 =~ fs_inv table -> 
                mk_inv table (mk_mul table a r2),True

              (*  a/a -> 1 (if a <> 0) *)
              | _ when conv r2 r1 && not_is_zero table r1 -> one, True 
              | _ -> t, NeedSub
          end
        | _ -> t, NeedSub
    in

    if not (st.red_param.builtin) then t, False
    else
      let t, has_red = reduce_int t in
      if has_red = True then t, has_red 
      else reduce_real t


  (** Rewrite once at head position *)
  and rewrite_head1 (st : state) (t : Term.term) : Term.term * head_has_red =
    if not st.red_param.rewrite then t, False 
    else
      let env = st.pc.env in
      let params = Env.to_params env in
      let db = Hint.get_rewrite_db env.table in
      let hints = Term.Hm.find_dflt [] (Term.get_head t) db in

      let rule = List.find_map (fun Hint.{ cnt = rule } ->
          match 
            Rewrite.rewrite_head
              ~param:Match.default_param ~concrete:st.pc.concrete
              (* no reduction here, to keep performances reasonable *)
              env.table params env.vars st.pc.hyps env.system.set
              rule t 
          with
          | None -> None
          | Some (red_t, subs) ->
            let subs_valid =  
              List.for_all (fun (se, sub) -> 
                  let new_context = { st.pc.env.system with set = se; } in
                  let st_sub =
                    { (change_context new_context st) with red_param = rp_default; } 
                  in
                  (* FEATURE: conversion *)
                  Term.equal
                    (fst (reduce_term st_sub sub))
                    Term.mk_true
                ) subs
            in              
            if subs_valid then Some red_t else None            
        ) hints
      in

      match rule with
      | None -> t, NeedSub
      | Some red_t -> red_t, True

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
        let vars = Vars.Tag.local_vars evs in
        f_red (add_vars vars st) t0
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

      let st_t = add_hyp c st in
      let st_f = add_hyp (Term.mk_not ~simpl:true c) st in

      let t, has_red1 = f_red st_t t in
      let e, has_red2 = f_red st_f e in

      Term.mk_fun0 fs fty [c; t; e],
      has_red0 || has_red1 || has_red2

    (* [φ => ψ] *)
    | Term.App (Fun (fs, fty), [f1;f2]) when fs = Term.f_impl -> 
      let st2 = add_hyp f1 st in

      let f1, has_red1 = f_red st  f1 in
      let f2, has_red2 = f_red st2 f2 in      

      Term.mk_fun0 fs fty [f1;f2],
      has_red1 || has_red2

    (* [φ && ψ] is handled as [φ && (φ => ψ)] *)
    | Term.App (Fun (fs, fty), [f1;f2]) when fs = Term.f_and -> 
      let st2 = add_hyp f1 st in

      let f1, has_red1 = f_red st  f1 in
      let f2, has_red2 = f_red st2 f2 in      

      Term.mk_fun0 fs fty [f1;f2],
      has_red1 || has_red2

    (* [φ || ψ] is handled as [φ || (¬ φ => ψ)] *)
    | Term.App (Fun (fs, fty), [f1;f2]) when fs = Term.f_or -> 
      let st2 = add_hyp (Term.mk_not f1) st in

      let f1, has_red1 = f_red st  f1 in
      let f2, has_red2 = f_red st2 f2 in      

      Term.mk_fun0 fs fty [f1;f2],
      has_red1 || has_red2

    | Term.Find (is, c, t, e) -> 
      let _, subst = Term.refresh_vars is in
      let c, t = Term.subst subst c, Term.subst subst t in
      let st1 = add_vars (Vars.Tag.local_vars is) st in

      let c, has_red0 = f_red st1 c in

      let st_t = add_hyp c st1 in
      let st_f =
        add_hyp (Term.mk_forall is (Term.mk_not ~simpl:true c)) st
      in

      let t, has_red1 = f_red st_t t in
      let e, has_red2 = f_red st_f e in

      let r_subst = rev_subst subst in
      let c, t = Term.subst r_subst c, Term.subst r_subst t in

      Term.mk_find ~simpl:true is c t e,
      has_red0 || has_red1 || has_red2

    | Term.Diff (Explicit l) -> 
      let has_red, l = 
        List.map_fold (fun has_red (label,t) ->
            let system = st.pc.env.system in
            let new_context = 
              { system with set = SE.project [label] system.set; }
            in
            let st = change_context new_context st in
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
  let reduce_glob_let1 (st : state) (t : Equiv.form) : Equiv.form * head_has_red =
    if not st.red_param.zeta then t, False
    else Match.reduce_glob_let1 t

  (*------------------------------------------------------------------*)
  (** Reduce once at head position in a global formula.
      May use all reduction rules:
       [zeta ] *)
  let reduce_head1_global
      (st : state) (t : Equiv.form) : Equiv.form * head_has_red
    = 
    let rec try_red red_funcs ~(has_red : head_has_red) =
      match red_funcs with
      | [] -> t, has_red
      | red_f :: red_funcs ->
        let t0, has_red0 = red_f t in
        if has_red0 = True then t0, True
        else
          let has_red = has_red ||| has_red0 in
          try_red red_funcs ~has_red
    in
    try_red ~has_red:False [reduce_glob_let1 st; ]     (* zeta *)

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
      let table = st.rst.pc.env.table in
      conv_tys p1.ty_args p2.ty_args;
      conv_systems table p1.se_args p2.se_args;

      List.iter2 (fun (se1,l1) (se2,l2) ->
          assert (SE.equal table se1 se2);
          let system = SE.{set = (se1 :> SE.t); pair = None; } in
          conv_l {st with rst = (change_context system st.rst)} l1 l2
        ) p1.multi_args p2.multi_args;

      let system = SE.{set = (SE.of_list [] :> SE.t); pair = None; } in
      (* FEAT: concrete: we could be more precise depending on whether
         the predicate is fully asymptotic or not (see
         [occurrence_kind] in [rewrite.ml]) *)
      conv_l {st with rst = (change_context system st.rst)} p1.simpl_args p2.simpl_args

    | Equiv.Atom (Reach f1), Equiv.Atom (Reach f2) ->
      let concrete = f1.bound <> None in
      let system = SE.{set = st.rst.pc.env.system.set; pair = None; } in
      let st = 
        let rst = 
          change_context system st.rst |> 
          set_concrete concrete
        in
        {st with rst} 
      in
      let st_b = {st with rst = set_concrete true st.rst} in
      conv     st   f1.formula f2.formula;
      conv_opt st_b f1.bound f2.bound

    | Equiv.Atom (Equiv ts1), Equiv.Atom (Equiv ts2) ->
      let concrete = ts1.bound <> None in
      let system =
        SE.{set = (oget st.rst.pc.env.system.pair :> SE.arbitrary); pair = None; }
      in
      let st = 
        let rst = 
          change_context system st.rst |>
          set_concrete concrete 
        in
        {st with rst} 
      in
      let st_b = {st with rst = set_concrete true st.rst} in
      conv_l   st   ts1.terms ts2.terms;
      conv_opt st_b ts1.bound ts2.bound;

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
    ?system:SE.context ->
    ?vars:Vars.env ->
    red_param -> ?concrete:bool -> t -> state

  (*------------------------------------------------------------------*)
  val reduce_global : 
    ?system:SE.context -> 
    red_param -> t -> Equiv.form -> Equiv.form

  val reduce : 
    ?system:SE.context -> 
    red_param -> ?concrete:bool -> t -> 'a Equiv.f_kind -> 'a -> 'a

  (** reduces once at head position *)
  val reduce_head1 :
    ?system:SE.context -> 
    red_param -> ?concrete:bool -> t -> 'a Equiv.f_kind -> 'a -> 'a * head_has_red

  (*------------------------------------------------------------------*)
  (** {2 expantion and destruction modulo } *)

  val destr_eq : 
    ?concrete:bool -> t ->
    'a Equiv.f_kind -> 'a -> (Term.term * Term.term) option

  val destr_not : 
    ?concrete:bool -> t ->
    'a Equiv.f_kind -> 'a -> Term.term option

  val destr_or : 
    ?concrete:bool -> t ->
    'a Equiv.f_kind -> 'a -> ('a * 'a) option

  val destr_and : 
    ?concrete:bool -> t ->
    mode:SmartFO.mode -> 'a Equiv.f_kind -> 'a -> ('a * 'a) option

  (*------------------------------------------------------------------*)
  (** {2 conversion from a sequent } *)

  val conv_term : 
    ?system:SE.context -> 
    ?param:red_param -> ?concrete:bool ->
    t ->
    Term.term -> Term.term -> bool

  val conv_global : 
    ?system:SE.context -> 
    ?param:red_param ->
    t ->
    Equiv.form -> Equiv.form -> bool

  val conv_kind : 
    ?system:SE.context -> 
    ?param:red_param -> ?concrete:bool ->
    t -> 'a Equiv.f_kind ->
    'a -> 'a -> bool
end

module Mk (S : LowSequent.S) : S with type t := S.t = struct

  (*------------------------------------------------------------------*)
  (** Build a convertion state from a sequent. 
      [system] is the system of the term being reduced. *)
  let to_state
      ?(system   : SE.context option)
      ?(vars     : Vars.env option) (* overloads [s] variables *)
      (red_param : red_param)
      ?(concrete : bool = true) (* safer option *)
      (s         : S.t)
    : state
    =
    let pc = S.proof_context ?in_system:system ~concrete s in
    let pc =
      omap_dflt pc (fun vars -> ProofContext.set_vars vars pc) vars
    in
    { pc; red_param; } 

  (*------------------------------------------------------------------*)
  (** Exported.
      We need type introspection here. *)
  let reduce_head1 (type a) 
      ?(system : SE.context option)
      (param : red_param) ?(concrete:bool option) (s : S.t)
      (k : a Equiv.f_kind) (x : a) : a * head_has_red
    =
    let st = to_state ?system ?concrete param s in
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
            let state = to_state ~system ~vars ~concrete:true param s in
            (* FEAT: concrete: we could be more precise depending on
               whether [f] is fully asymptotic or not (see
               [occurrence_kind] in [rewrite.ml]) *)
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
        let concrete = f.bound <> None in
        let state = to_state ~system ~vars ~concrete param s in
        let f_form = reduce_term state f.formula in
        let f_bound = 
          let state = set_concrete true state in
          Utils.omap (reduce_term state) f.bound 
        in
        Equiv.Atom (Reach {formula =f_form; bound = f_bound})

      | Equiv.Atom (Equiv e) ->
        let concrete = e.bound <> None in
        let system = { system with set = (oget system.pair :> SE.t); } in
        let state = to_state ~system ~vars ~concrete param s in

        let b_se = (SE.context_any) in
        let b_state = to_state ~system:b_se ~vars ~concrete:true param s in

        let e_terms = List.map   (reduce_term   state) e.terms in
        let e_bound = Utils.omap (reduce_term b_state) e.bound in
        Equiv.Atom (Equiv.Equiv {terms = e_terms; bound = e_bound})

      | Equiv.Atom (Pred pa) ->
        let simpl_args =
          (* terms in [simpl_args] are single terms (thus [k=1])
             defined in no systems (thus the empty system) *)
          let system = { system with set = (SE.fset_empty ~k:1 env.table :> SE.t); } in
          let state = to_state ~system ~vars ~concrete:true param s in
          (* FEAT: concrete: we could be more precise depending on
             whether the atom is fully asymptotic or not (see
             [occurrence_kind] in [rewrite.ml]) *)
          List.map (reduce_term state) pa.simpl_args
        in
        let multi_args =
          List.map (fun (se,args) ->
              let system = { system with set = se; } in
              let state = to_state ~system ~vars ~concrete:true param s in
              (* FEAT: concrete: idem *)
              ( se, List.map (reduce_term state) args )
            ) pa.multi_args
        in
        Equiv.Atom (Equiv.Pred { pa with simpl_args; multi_args; })
    in
    reduce_g (S.vars s) e

  (*------------------------------------------------------------------*)
  (** We need type introspection there *)
  let reduce (type a) 
      ?(system : SE.context option)
      (param : red_param) ?(concrete : bool option)
      (s : S.t) (k : a Equiv.f_kind) (x : a) : a 
    =
    let reduce_term x = 
      let st = to_state ?system param ?concrete s in
      reduce_term st x
    in
    let reduce_global x =
      reduce_global ?system param s x
    in
    match k with
    | Local_t  -> reduce_term   x
    | Global_t -> reduce_global x
    | Any_t ->
      match x with
      | Local  x -> Local  (reduce_term   x)
      | Global x -> Global (reduce_global x)

  (*------------------------------------------------------------------*)
  (** Destruct [x] according to an arbitrary destruct function [destr_f], 
      using [s] to reduce [x] if necessary. *)
  let mk_destr (type a)
      ?(concrete : bool option)
      (destr_f : Term.term -> 'b option)
      (s : S.t) (k : a Equiv.f_kind)
      (x : a) : 'b option
    =
    let rec destr_term (x : Term.term) =
      match destr_f x with
      | Some _ as res -> res
      | None ->
        let x, has_red = reduce_head1_term (to_state rp_full ?concrete s) x in
        if has_red <> True then 
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
      ?(concrete : bool option)
      (destr_t0 : Term.term  -> (Term.term  * Term.term ) option)
      (destr_e0 : Equiv.form -> (Equiv.form * Equiv.form) option)
      (s : S.t) (k : a Equiv.f_kind)
      (x : a) : (a * a) option
    =
    let rec destr_t (x : Term.term) =
      match destr_t0 x with
      | Some _ as res -> res
      | None ->
        let x, has_red = reduce_head1_term (to_state rp_full ?concrete s) x in
        if has_red <> True then 
          None               (* did not reduce, failed *)
        else
          destr_t x          (* reduced, recurse to try again *)
    in
    let rec destr_e (x : Equiv.form) =
      match destr_e0 x with
      | Some _ as res -> res
      | None ->
        let x, has_red = reduce_head1_global (to_state rp_full ?concrete s) x in
        if has_red <> True then 
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
      ?(concrete : bool option)
      (s : S.t) (k : a Equiv.f_kind)
      (x : a) : (Term.term * Term.term) option
    =
    let destr_eq_or_iff x =
      match Term.destr_eq x with
      | Some _ as res -> res
      | None -> Term.destr_iff x
    in
    mk_destr ?concrete destr_eq_or_iff s k x

  let destr_not (type a)
      ?(concrete : bool option)
      (s : S.t) (k : a Equiv.f_kind)
      (x : a) : Term.term option
    =
    mk_destr ?concrete Term.destr_not s k x

  (*------------------------------------------------------------------*)
  let destr_or (type a)
      ?(concrete : bool option)
      (s : S.t) (k : a Equiv.f_kind)
      (x : a) : (a * a) option
    =
    mk_destr_k ?concrete Term.destr_or (Equiv.Smart.destr_or ~env:(S.env s)) s k x

  (*------------------------------------------------------------------*)
  let destr_and (type a)
      ?(concrete : bool option)
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
    mk_destr_k ?concrete destr_and (Equiv.Smart.destr_and ~mode ~env:(S.env s)) s k x

  (*------------------------------------------------------------------*)
  (** Exported. *)
  let conv_term
      ?(system : SE.context option)
      ?(param : red_param = rp_default)
      ?(concrete : bool option)
      (s : S.t)
      (t1 : Term.term) (t2 : Term.term) : bool
    =
    let state = to_state ?system param ?concrete s in
    conv state t1 t2

  (** Exported. *)
  let conv_global
      ?(system : SE.context option)
      ?(param : red_param = rp_default)
      (s : S.t)
      (e1 : Equiv.form) (e2 : Equiv.form) : bool
    =
    let state = to_state ?system param s in
    conv_g state e1 e2

  (** We need type introspection there *)
  let conv_kind (type a) 
      ?(system : SE.context option)
      ?(param : red_param = rp_default)
      ?(concrete : bool option)
      (s : S.t) (k : a Equiv.f_kind)
      (x1 : a) (x2 : a) : bool
    =
    match k with
    | Local_t  -> conv_term   ?system ~param ?concrete s x1 x2
    | Global_t -> conv_global ?system ~param           s x1 x2
    | Any_t ->
      match x1, x2 with
      | Local  x1, Local  x2 -> conv_term   ?system ~param ?concrete s x1 x2
      | Global x1, Global x2 -> conv_global ?system ~param           s x1 x2
      | _, _ -> false

end

