open Utils
open Term

module Sv = Vars.Sv
module Mv = Vars.Mv

(*------------------------------------------------------------------*)
(** {2 Matching and rewriting} *)

(** A pattern is a list of free type variables, a term [t] and a subset
    of [t]'s free variables that must be matched.
    The free type variables must be inferred. *)
type 'a pat = {
  pat_tyvars : Type.tvars;
  pat_vars   : Vars.Sv.t;
  pat_term   : 'a;
}

let pat_of_form (t : 'a term) =
  let vs, t = decompose_forall t in
  let vs, s = erefresh_vars `Global vs in
  let t = subst s t in

  { pat_tyvars = [];
    pat_vars = Vars.Sv.of_list vs;
    pat_term = t; }

(*------------------------------------------------------------------*)
(** Matching variable assignment (types must be compatible). *)
module Mvar = struct
  type t = eterm Mv.t

  let empty = Mv.empty

  let union mv1 mv2 = Mv.union (fun _ _ _ -> assert false) mv1 mv2

  let add (v : Vars.evar) (t : eterm) (m : t) : t = Mv.add v t m

  let remove (v : Vars.evar) (m : t) : t = Mv.remove v m

  let mem (v : Vars.evar) (m : t) : bool = Mv.mem v m

  let is_empty (m : t) = Mv.is_empty m

  let filter f (m : t) : t = Mv.filter f m

  let fold f (m : t) (init : 'b) : 'b = Mv.fold f m init

  let to_subst ~(mode:[`Match|`Unif]) (mv : t) : subst =
    let s =
      Mv.fold (fun v t subst ->
          match v, t with
          | Vars.EVar v, ETerm t ->
            ESubst (Var v, cast (Vars.kind v) t) :: subst
        ) mv []
    in

    match mode with
    | `Match -> s
    | `Unif ->
      (* We need to substitute until we reach a fixpoint *)
      let support = Mv.fold (fun v _ supp -> Sv.add v supp) mv Sv.empty in
      let rec fp_subst t =
        if Sv.disjoint (fv t) support then t
        else fp_subst (subst s t)
      in
      List.map (fun (ESubst (v, t)) -> ESubst (v, fp_subst t)) s

end
(*------------------------------------------------------------------*)
(** (Descending) state used in the matching algorithm. *)
type match_state = {
  mv  : Mvar.t;          (** inferred variable assignment *)
  bvs : Sv.t;            (** bound variables "above" the current position *)

  support  : Sv.t;       (** free variable which we are trying to match *)
  env      : Sv.t;       (** rigid free variables (disjoint from [support]) *)
  table    : Symbols.table;
  system   : SystemExpr.t;
}

(*------------------------------------------------------------------*)
(** (Descending) state used in the unification algorithm. *)
type unif_state = {
  mv       : Mvar.t;     (** inferred variable assignment *)
  bvs      : Sv.t;       (** bound variables "above" the current position *)

  subst_vs : Sv.t;       (** vars already substituted (for cycle detection) *)

  support  : Sv.t;       (** free variable which we are trying to unify *)
  env      : Sv.t;       (** rigid free variables (disjoint from [support]) *)
  table    : Symbols.table;
}


(*------------------------------------------------------------------*)
(** Module signature of matching.
    The type of term we match into is abstract. *)
module type S = sig
  type t

  val pp_pat :
    (Format.formatter -> 'a -> unit) ->
    Format.formatter -> 'a pat -> unit

  val unify :
    ?mv:Mvar.t ->
    Symbols.table ->
    t pat -> t pat ->
    [`FreeTyv | `NoMgu | `Mgu of Mvar.t]

  val unify_opt :
    ?mv:Mvar.t ->
    Symbols.table ->
    t pat -> t pat ->
    Mvar.t option

  val try_match :
    ?mv:Mvar.t ->
    ?mode:[`Eq | `EntailLR | `EntailRL] ->
    Symbols.table ->
    SystemExpr.t ->
    t -> t pat ->
    [ `FreeTyv | `NoMatch | `Match of Mvar.t ]

  val try_match_term :
    ?mv:Mvar.t ->
    ?mode:[`Eq | `EntailLR | `EntailRL] ->
    Symbols.table ->
    SystemExpr.t ->
    'a term -> 'b term pat ->
    [ `FreeTyv | `NoMatch | `Match of Mvar.t ]

  val find_map :
    many:bool ->
    Symbols.table ->
    SystemExpr.t ->
    Vars.env ->
    t -> 'a term pat ->
    ('a term -> Vars.evars -> Mvar.t -> 'a term) ->
    t option
end

module T : S with type t = message = struct
  type t = message

  let pp_pat pp_t fmt p =
    Fmt.pf fmt "@[<hov 0>{term = @[%a@];@ tyvars = @[%a@];@ vars = @[%a@]}@]"
      pp_t p.pat_term
      (Fmt.list ~sep:Fmt.sp Type.pp_tvar) p.pat_tyvars
      (Fmt.list ~sep:Fmt.sp Vars.pp_e) (Sv.elements p.pat_vars)

  (* Remark: unsurprisingly, the unification and matching function are
     very similar. *)
  let unify
      ?mv:mv
      (table : Symbols.table)
      (t1 : t pat)
      (t2 : t pat) : [`FreeTyv | `NoMgu | `Mgu of Mvar.t]
    =
    let exception NoMgu in

    (* [ty_env] must be closed at the end of the matching *)
    let ty_env = Type.Infer.mk_env () in

    let univars1, ty_subst1 = Type.Infer.open_tvars ty_env t1.pat_tyvars in
    let term1 = tsubst ty_subst1 t1.pat_term in

    let univars2, ty_subst2 = Type.Infer.open_tvars ty_env t2.pat_tyvars in
    let term2 = tsubst ty_subst2 t2.pat_term in

    (* substitute back the univars by the corresponding tvars *)
    let ty_subst_rev : Type.tsubst =
      let tysubst =
        List.fold_left2 (fun s tv tu ->
            Type.tsubst_add_univar s tu (Type.TVar tv)
          ) Type.tsubst_empty t1.pat_tyvars univars1
      in
      List.fold_left2 (fun s tv tu ->
          Type.tsubst_add_univar s tu (Type.TVar tv)
        ) tysubst t2.pat_tyvars univars2
    in

    let supp1 = Sv.map (Vars.tsubst_e ty_subst1) t1.pat_vars in
    let supp2 = Sv.map (Vars.tsubst_e ty_subst2) t2.pat_vars in
    let support = Sv.union supp1 supp2 in

    let env = Sv.diff (Sv.union (Term.fv term1) (Term.fv term2)) support in

    (* Invariants:
       - [st.mv] supports in included in [unif_support].
       - [st.bvs] is the set of variables bound above [t].
       - [st.bvs] must be disjoint from the free variables of the terms in the
         co-domain of [mv]. *)
    let rec unif : type a. a term -> a term -> unif_state -> Mvar.t =
      fun t1 t2 st ->
        match t1, t2 with
        | Var v, t | t, Var v ->
          vunif t v st

        | Fun (symb, _, terms), Fun (symb', _, terms') ->
          let mv = sunif symb symb' st in
          unif_l terms terms' { st with mv }

        | Name s, Name s' -> isymb_unif s s' st

        | Macro (s, terms, ts),
          Macro (s', terms', ts') ->
          let mv = isymb_unif s s' st in
          assert (Type.equal s.s_typ s'.s_typ);

          let mv = unif_l terms (terms') { st with mv } in
          unif ts ts' { st with mv }

        | Pred ts, Pred ts' -> unif ts ts' st

        | Action (s,is), Action (s',is') -> sunif (s,is) (s',is') st

        | Diff (a,b), Diff (a', b') ->
          unif_l [a;b] [a';b'] st

        | Atom at, Atom at' -> atunif at at' st

        | Find (is, c, t, e), Find (is', pat_c, pat_t, pat_e) ->
          let is  = List.map Vars.evar is
          and is' = List.map Vars.evar is' in
          let s, s', st = unif_bnds is is' st in

          let c    ,     t = subst s      c, subst s      t
          and pat_c, pat_t = subst s' pat_c, subst s' pat_t in
          unif_l [c; t; e] [pat_c; pat_t; pat_e] st

        | Seq (is, t), Seq (is', pat) ->
          let is  = List.map Vars.evar is  in
          let is' = List.map Vars.evar is' in
          let s, s', st = unif_bnds is is' st in

          let t   = subst s    t in
          let pat = subst s' pat in

          unif t pat st

        | Exists (vs,t), Exists (vs', pat)
        | ForAll (vs,t), ForAll (vs', pat) ->
          let s, s', st = unif_bnds vs vs' st in
          let t   = subst s    t in
          let pat = subst s' pat in
          unif t pat st

        | _, _ -> raise NoMgu

    (* Return: left subst, right subst, unification state *)
    and unif_bnds (vs : Vars.evars) (vs' : Vars.evars) st :
      esubst list * esubst list * unif_state =
      if List.length vs <> List.length vs' then
        raise NoMgu;

      (* check that types are compatible *)
      List.iter2 (fun (Vars.EVar v) (Vars.EVar v') ->
          let ty, ty' = Vars.ty v, Vars.ty v' in
          match Type.equal_w ty ty' with
          | None -> raise NoMgu
          | Some Type.Type_eq ->
            if Type.Infer.unify_eq ty_env ty ty' = `Fail then
              raise NoMgu;
        ) vs vs';

      (* refresh [vs] *)
      let vs, s = erefresh_vars `Global vs in

      (* refresh [vs'] using the same renaming *)
      let s' = List.map2 (fun (ESubst (_, new_v)) (Vars.EVar v') ->
          match Type.equal_w (ty new_v) (Vars.ty v') with
          | None -> assert false
          | Some Type.Type_eq -> ESubst (Var v', new_v)
        ) (List.rev s)          (* reversed ! *)
          vs'
      in

      (* update [bvs] *)
      let st = { st with bvs = Sv.union st.bvs (Sv.of_list vs) } in

      s, s', st

    (* unify a variable and a term. *)
    and vunif : type a. a term -> a Vars.var -> unif_state -> Mvar.t =
      fun t v st ->
        let v, t = match t with
          | Var v' ->
            if not (Sv.mem (Vars.evar v) st.support) then
              v', Var v
            else if not (Sv.mem (Vars.evar v') st.support) then
              v, t
            else if Vars.compare v v' < 0 then
              v, t
            else
              v', Var v

          | _ -> v, t
        in
        let ev = Vars.EVar v in

        if not (Sv.mem ev st.support)
        then if t = Var v then st.mv else raise NoMgu

        else (* [v] in the support, and [v] smaller than [v'] if [t = Var v'] *)
          match Mv.find ev st.mv with
          (* first time we see [v]: store the substitution and add the
             type information. *)
          | exception Not_found ->
            if Type.Infer.unify_eq ty_env (ty t) (Vars.ty v) = `Fail then
              raise NoMgu;

            (* check that we are not trying to unify [v] with a term using
               bound variables. *)
            if not (Sv.disjoint (fv t) st.bvs) then raise NoMgu;

            (Mv.add ev (ETerm t) st.mv)

          (* If we already saw the variable, check that there is no cycle, and
             call back [unif]. *)
          | ETerm t' -> match cast (kind t) t' with
            | exception Uncastable -> raise NoMgu
            | t' ->
              if Sv.mem ev st.subst_vs then raise NoMgu
              else
                let st =
                  { st with subst_vs = Sv.add ev st.subst_vs }
                in
                unif t t' st

    (** unifies an atom *)
    and atunif (at : generic_atom) (at' : generic_atom) st : Mvar.t =
      match at, at' with
      | `Message (ord, t1, t2), `Message (ord', t1', t2') ->
        if ord <> ord' then raise NoMgu;
        unif_l [t1;t2] [t1';t2'] st

      | `Timestamp (ord, t1, t2), `Timestamp (ord', t1', t2') ->
        if ord <> ord' then raise NoMgu;
        unif_l [t1;t2] [t1';t2'] st

      | `Index (ord, t1, t2), `Index (ord', t1', t2') ->
        if ord <> ord' then raise NoMgu;
        unif_l [Var t1; Var t2] [Var t1'; Var t2'] st

      | `Happens ts, `Happens ts' -> unif ts ts' st

      | _, _ -> raise NoMgu

    and unif_l : type a.
      a term list -> a term list -> unif_state -> Mvar.t =
      fun tl1 tl2 st ->
        List.fold_left2 (fun mv t1 t2 ->
            unif t1 t2 { st with mv }
          ) st.mv tl1 tl2

    (** unif an [i_symb].
       Note: types are not checked. *)
    and isymb_unif : type a b c.
      ((a Symbols.t, b) isymb) ->
      ((a Symbols.t, c) isymb) ->
      unif_state -> Mvar.t =
      fun s s' st ->
        sunif (s.s_symb,s.s_indices) (s'.s_symb, s'.s_indices) st

    (** unif a symbol (with some indices) *)
    and sunif : type a.
      (a Symbols.t * Vars.index list) ->
      (a Symbols.t * Vars.index list) ->
      unif_state -> Mvar.t =
      fun (fn, is) (fn', is') st ->
        if fn <> fn' then raise NoMgu;

        List.fold_left2 (fun mv i i' ->
            vunif (Var i) i' { st with mv }
          ) st.mv is is'
    in

    let mv_init = odflt Mv.empty mv in
    let st_init = {
      subst_vs = Sv.empty;
      bvs = Sv.empty;
      mv = mv_init ;
      support;
      env;
      table;
    } in

    try
      let mv = unif term1 term2 st_init in

      if not (Type.Infer.is_closed ty_env)
      then `FreeTyv
      else
        let mv =
          Mv.fold (fun (Vars.EVar v) t mv ->
              let v = Vars.tsubst ty_subst_rev v in
              Mv.add (Vars.EVar v) t mv
            ) mv Mv.empty
        in
        `Mgu mv

    with NoMgu -> `NoMgu


  (*------------------------------------------------------------------*)
  let unify_opt
      ?mv:mv
      (table : Symbols.table)
      (t1 : t pat)
      (t2 : t pat) : Mvar.t option
    =
    match unify ?mv table t1 t2 with
    | `FreeTyv | `NoMgu -> None
    | `Mgu mv -> Some mv

  (*------------------------------------------------------------------*)
  let try_match_term : type a b.
    ?mv:Mvar.t ->
    ?mode:[`Eq | `EntailLR | `EntailRL] ->
    Symbols.table ->
    SystemExpr.t ->
    a term -> b term pat ->
    [`FreeTyv | `NoMatch | `Match of Mvar.t] =
    fun ?mv ?mode table system t p ->
    let exception NoMatch in

    (* Term matching ignores [mode]. Matching in [Equiv] does not. *)

    (* [ty_env] must be closed at the end of the matching *)
    let ty_env = Type.Infer.mk_env () in
    let univars, ty_subst  = Type.Infer.open_tvars ty_env p.pat_tyvars in
    let pat = tsubst ty_subst p.pat_term in

    (* substitute back the univars by the corresponding tvars *)
    let ty_subst_rev =
      List.fold_left2 (fun s tv tu ->
          Type.tsubst_add_univar s tu (Type.TVar tv)
        ) Type.tsubst_empty p.pat_tyvars univars
    in

    let support = Sv.map (Vars.tsubst_e ty_subst) p.pat_vars in
    let env = Sv.diff (Sv.union (Term.fv t) (Term.fv pat)) support in

    (* Invariants:
       - [st.mv] supports in included in [p.pat_vars].
       - [st.bvs] is the set of variables bound above [t].
       - [st.bvs] must be disjoint from the free variables of the terms in the
         co-domain of [mv]. *)
    let rec tmatch : type a b. a term -> b term -> match_state -> Mvar.t =
      fun t pat st ->
        match t, pat with
        | _, Var v' ->
          begin
            match cast (Vars.kind v') t with
            | exception Uncastable -> raise NoMatch
            | t -> vmatch t v' st
          end

        | Fun (symb, fty, terms), Fun (symb', fty', terms') ->
          let mv = smatch symb symb' st in
          tmatch_l terms terms' { st with mv }

        | Name s, Name s' -> isymb_match s s' st

        | Macro (s, terms, ts),
          Macro (s', terms', ts') ->
          let mv = isymb_match s s' st in
          assert (Type.equal s.s_typ s'.s_typ);

          let mv = tmatch_l terms terms' { st with mv } in
          tmatch ts ts' { st with mv }

        | Pred ts, Pred ts' -> tmatch ts ts' st

        | Action (s,is), Action (s',is') -> smatch (s,is) (s',is') st

        | Diff (a,b), Diff (a', b') ->
          tmatch_l [a;b] [a';b'] st

        | Atom at, Atom at' -> atmatch at at' st

        | Find (is, c, t, e), Find (is', pat_c, pat_t, pat_e) ->
          let is  = List.map Vars.evar is
          and is' = List.map Vars.evar is' in
          let s, s', st = match_bnds is is' st in

          let c    ,     t = subst s      c, subst s      t
          and pat_c, pat_t = subst s' pat_c, subst s' pat_t in
          tmatch_l [c; t; e] [pat_c; pat_t; pat_e] st

        | Seq (is, t), Seq (is', pat) ->
          let is  = List.map Vars.evar is  in
          let is' = List.map Vars.evar is' in
          let s, s', st = match_bnds is is' st in

          let t   = subst s    t in
          let pat = subst s' pat in

          tmatch t pat st

        | Exists (vs,t), Exists (vs', pat)
        | ForAll (vs,t), ForAll (vs', pat) ->
          let s, s', st = match_bnds vs vs' st in
          let t   = subst s    t in
          let pat = subst s' pat in
          tmatch t pat st

        | _, _ -> raise NoMatch

    (* Return: left subst, right subst, match state *)
    and match_bnds (vs : Vars.evars) (vs' : Vars.evars) st :
      esubst list * esubst list * match_state =
      if List.length vs <> List.length vs' then
        raise NoMatch;

      (* check that types are compatible *)
      List.iter2 (fun (Vars.EVar v) (Vars.EVar v') ->
          let ty, ty' = Vars.ty v, Vars.ty v' in
          match Type.equal_w ty ty' with
          | None -> raise NoMatch
          | Some Type.Type_eq ->
            if Type.Infer.unify_eq ty_env ty ty' = `Fail then
              raise NoMatch;
        ) vs vs';

      (* refresh [vs] *)
      let vs, s = erefresh_vars `Global vs in

      (* refresh [vs'] using the same renaming *)
      let s' = List.map2 (fun (ESubst (_, new_v)) (Vars.EVar v') ->
          match Type.equal_w (ty new_v) (Vars.ty v') with
          | None -> assert false
          | Some Type.Type_eq -> ESubst (Var v', new_v)
        ) (List.rev s)          (* reversed ! *)
          vs'
      in

      (* update [bvs] *)
      let st = { st with bvs = Sv.union st.bvs (Sv.of_list vs) } in

      s, s', st

    and tmatch_l : type a b.
      a term list -> b term list -> match_state -> Mvar.t =
      fun tl patl st ->
        List.fold_left2 (fun mv t pat ->
            tmatch t pat { st with mv }
          ) st.mv tl patl

    (* match an [i_symb].
       Note: types are not checked. *)
    and isymb_match : type a b c.
      ((a Symbols.t, b) isymb) ->
      ((a Symbols.t, c) isymb) ->
      match_state -> Mvar.t =
      fun s s' st ->
        smatch (s.s_symb,s.s_indices) (s'.s_symb, s'.s_indices) st

    (* match a symbol (with some indices) *)
    and smatch : type a.
      (a Symbols.t * Vars.index list) ->
      (a Symbols.t * Vars.index list) ->
      match_state -> Mvar.t =
      fun (fn, is) (fn', is') st ->
        if fn <> fn' then raise NoMatch;
        
        List.fold_left2 (fun mv i i' -> 
            vmatch (Var i) i' { st with mv }
          ) st.mv is is'


    (* Match a variable of the pattern with a term. *)
    and vmatch : type a. a term -> a Vars.var -> match_state -> Mvar.t =
      fun t v st ->
        let ev = Vars.EVar v in

        if not (Sv.mem ev p.pat_vars)
        then (* [v] not in the pattern *)
          if t = Var v then st.mv else raise NoMatch 

        else (* [v] in the pattern *)
          match Mv.find ev st.mv with
          (* If this is the first time we see the variable, store the subterm
             and add the type information. *)
          | exception Not_found ->
            if Type.Infer.unify_eq ty_env (ty t) (Vars.ty v) = `Fail then
              raise NoMatch;

            (* check that we are not trying to match [v] with a term free bound
               variables. *)
            if not (Sv.disjoint (fv t) st.bvs) then raise NoMatch;

            Mv.add ev (ETerm t) st.mv 

          (* If we already saw the variable, check that the subterms are
             identical. *)
          | ETerm t' -> match cast (kind t) t' with
            | exception Uncastable -> raise NoMatch
            (* TODO: alpha-equivalent *)
            | t' -> if t <> t' then raise NoMatch else st.mv

    (* matches an atom *)
    and atmatch (at : generic_atom) (at' : generic_atom) st : Mvar.t =
      match at, at' with
      | `Message (ord, t1, t2), `Message (ord', t1', t2') ->
        if ord <> ord' then raise NoMatch;
        tmatch_l [t1;t2] [t1';t2'] st

      | `Timestamp (ord, t1, t2), `Timestamp (ord', t1', t2') ->
        if ord <> ord' then raise NoMatch;
        tmatch_l [t1;t2] [t1';t2'] st

      | `Index (ord, t1, t2), `Index (ord', t1', t2') ->
        if ord <> ord' then raise NoMatch;
        tmatch_l [Var t1; Var t2] [Var t1'; Var t2'] st

      | `Happens ts, `Happens ts' -> tmatch ts ts' st

      | _, _ -> raise NoMatch
    in

    try
      let mv_init = odflt Mv.empty mv in
      let st_init : match_state =
        { bvs = Sv.empty; mv = mv_init; table; system; env; support; }
      in
      let mv = tmatch t pat st_init in

      if not (Type.Infer.is_closed ty_env)
      then `FreeTyv
      else
        let mv =
          Mv.fold (fun (Vars.EVar v) t mv ->
              let v = Vars.tsubst ty_subst_rev v in
              Mv.add (Vars.EVar v) t mv
            ) mv Mv.empty
        in
        `Match mv

    with NoMatch -> `NoMatch

  let try_match = try_match_term

  let find_map :
    type a b.
    many:bool ->
    Symbols.table ->
    SystemExpr.t ->
    Vars.env -> a term -> b term pat ->
    (b term -> Vars.evars -> Mvar.t -> b term) ->
    a term option
    = fun ~many table system env t p func ->
      let cut = ref false in
      let s_p = kind p.pat_term in

      (* the return boolean indicates whether a match was found in the subterm. *)
      let rec find : type a. Vars.env -> Vars.evars -> a term -> bool * a term =
        fun env vars t ->
        if !cut then false, t

        (* otherwise, check if head matches *)
        else
          match try_match table system t p with
          (* head matches *)
          | `Match mv ->
            cut := not many;    (* we cut if [many = false] *)
            let t' = func (cast s_p t) vars mv in
            true, cast (kind t) t'

          (* head does not match, recurse with a special handling of binders *)
          | `NoMatch | `FreeTyv ->
            match t with
            | ForAll (vs, b) ->
              let env, vs, s = erefresh_vars_env env vs in
              let b = subst s b in
              let found, b = find env (vars @ vs) b in
              let t' = cast (kind t) (ForAll (vs, b)) in

              if found then true, t' else false, t

            | Exists (vs, b) ->
              let env, vs, s = erefresh_vars_env env vs in
              let b = subst s b in
              let found, b = find env (vars @ vs) b in
              let t' = cast (kind t) (Exists (vs, b)) in

              if found then true, t' else false, t

            | Find (b, c, d, e) ->
              let env1, vs, s = refresh_vars_env env b in
              let c, d = subst s c, subst s e in
              let vars1 = vars @ (List.map Vars.evar b) in
              let found0, c = find env1 vars1 c in
              let found1, d = find env1 vars1 d in
              let found2, e = find env  vars  e in
              let t' = cast (kind t) (Find (b, c, d, e)) in
              let found = found0 || found1 || found2 in

              if found then true, t' else false, t

            | Seq (vs, b) ->
              let env1, vs, s = refresh_vars_env env vs in
              let b = subst s b in
              let vars = vars @ (List.map Vars.evar vs) in
              let found, b = find env vars b in
              let t' = cast (kind t) (Seq (vs, b)) in

              if found then true, t' else false, t

            | _ ->
              tmap_fold (fun found (ETerm t) ->
                  let found', t = find env vars t in
                  found || found', ETerm t
                ) false t
      in

      let found, t = find env [] t in
      match found with
      | false -> None
      | true  -> Some t
end

(*------------------------------------------------------------------*)
(** {2 Equiv Matching} *)


module E : S with type t = Equiv.form = struct
  module TMatch = T

  (* We include Term.Match, and redefine any necessary function *)
  include TMatch

  type t = Equiv.form

  (*------------------------------------------------------------------*)
  type ts_c = [
    | `TVar of Vars.timestamp
    | `Action of Symbols.action Symbols.t * Vars.index list
  ]

  let ts_of_ts_c = function
    | `TVar v -> Term.Var v
    | `Action (a, idx) -> Term.Action (a, idx)

  let ts_c_of_ts = function
    | Term.Action (a, is) ->
      `Action (a, is)
    | Term.Var tv -> `TVar tv
    | _ -> assert false

  let subst_ts_c subst ts_c =
    ts_c_of_ts (Term.subst subst (ts_of_ts_c ts_c))

  let pp_ts_c fmt ts_c = Term.pp fmt (ts_of_ts_c ts_c)

  (*------------------------------------------------------------------*)
  (** Set of terms over some indices with pending substitution.
      If the type variable ['a] is [Term.message list], then
        [{ term    = [t1; ...; tn];
           subst   = θ;
           indices = vars; }]
      represents the set of tuples of terms [\{(t1, ..., tn)θ | ∃ vars \}].

      The case ['a = Term.message] is identical to the case where
      ['a = Term.message list] and the list is of length 1.

      Note: [θ] supports is *not* always included in [indices]. *)
  type 'a cand_set_g = {
    term    : 'a;
    subst   : Mvar.t;
    indices : Vars.index list;
  }

  type cand_set       = Term.message  cand_set_g
  type cand_tuple_set = Term.messages cand_set_g

  type cand_sets   = cand_set   list
  type cand_tuple_sets = cand_tuple_set list

  (*------------------------------------------------------------------*)
  (** Set of terms over some indices and at most one timestamp variable.
        [{ term    = t;
           indices = vars;
           tvar    = τ;
           cond    = ψ; }]
      represents the set of terms [\{t | ∃ vars, τ. ψ \}]. *)
  type known_set = {
    term    : Term.message;
    indices : Vars.index list;
    tvar    : Vars.timestamp option;
    cond    : Term.message;
  }

  type known_sets = known_set list

  (*------------------------------------------------------------------*)
  module Mset : sig
    (** Set of macros over some indices.
          [{ msymb   = m;
             indices = vars; }]
        represents the set of terms [\{m@τ | ∃ vars \}] (for any τ). *)
    type t = private {
      msymb   : Term.msymb;
      indices : Vars.index list;
    }

    val mk :
      Sv.t ->
      msymb:Term.msymb ->
      indices:(Vars.index list) ->
      t
  end = struct
    type t = {
      msymb   : Term.msymb;
      indices : Vars.index list;
    }

    let mk (env : Sv.t) ~msymb ~indices : t =
      let indices = Sv.diff (Sv.of_list1 indices) env in
      let indices =
        List.map (fun ev -> Vars.ecast ev Type.KIndex) (Sv.elements indices)
      in
      { msymb; indices }
  end

  (** msets sorted in an association list *)
  type msets = (Term.mname * Mset.t list) list

  let msets_to_list (msets : msets) : Mset.t list =
    List.concat_map (fun (_, l) -> l) msets

  (*------------------------------------------------------------------*)
  let pp_mset fmt (mset : Mset.t) =
    let vars = List.map Vars.evar mset.indices in

    Fmt.pf fmt "@[<hv 2>{ @[%a@]@@_ |@ %a}@]"
      Term.pp_msymb mset.msymb
      (Fmt.list ~sep:Fmt.comma Vars.pp_e) vars

  let pp_mset_l fmt (mset_l : Mset.t list) =
    Fmt.pf fmt "@[<v 0>%a@]"
      (Fmt.list ~sep:Fmt.sp pp_mset) mset_l

  let pp_msets fmt (msets : msets) =
    let mset_l = msets_to_list msets in
    pp_mset_l fmt mset_l

  (*------------------------------------------------------------------*)
  let pp_cand_set pp_term fmt (cand : 'a cand_set_g) =
    let pp_subst fmt mv =
      let s = Mvar.to_subst ~mode:`Unif mv in
      if s = [] then ()
      else Fmt.pf fmt "[%a]" Term.pp_subst s
    in

    let vars = List.map Vars.evar cand.indices in

    Fmt.pf fmt "@[<hv 2>{ @[%a@]@[%a@] |@ %a}@]"
      pp_term cand.term
      pp_subst cand.subst
      (Fmt.list ~sep:Fmt.comma Vars.pp_e) vars

  (*------------------------------------------------------------------*)
  let pp_known_set fmt (known : known_set) =
    let tvs = match known.tvar with
      | None -> []
      | Some tv -> [Vars.evar tv]
    in
    let vars = tvs @ List.map Vars.evar known.indices in

    Fmt.pf fmt "@[<hv 2>{ @[%a@] |@ %a}@]"
      Term.pp known.term
      (Fmt.list ~sep:Fmt.comma Vars.pp_e) vars

  (*------------------------------------------------------------------*)
  let pat_of_cand_set (cand : cand_set) : Mvar.t * Term.message pat =
    cand.subst,
    { pat_term   = cand.term;
      pat_vars   = Sv.of_list1 cand.indices;
      pat_tyvars = []; }

  let pat_of_known_set (known : known_set) : Term.message pat =
    let vars =
      let tvs = match known.tvar with
        | None -> []
        | Some tv -> [tv]
      in
      Sv.add_list (Sv.of_list1 known.indices) tvs
    in
    { pat_term   = known.term;
      pat_vars   = vars;
      pat_tyvars = []; }

  (*------------------------------------------------------------------*)
  let msets_add (mset : Mset.t) (msets : msets) : msets =
    let name = mset.msymb.s_symb in
    if List.mem_assoc name msets then
      List.assoc_up name (fun b -> mset :: b) msets
    else (name, [mset]) :: msets

  (** [mset_entail tbl s1 s2] check if all terms in [s1] are
      members of [s2]. *)
  let mset_entail table system (s1 : Mset.t) (s2 : Mset.t) : bool
    =
    let tv = Vars.make_new Type.Timestamp "t" in
    let term1 = Term.Macro (s1.msymb, [], Term.Var tv) in
    let term2 = Term.Macro (s2.msymb, [], Term.Var tv) in

    let pat2 =
      { pat_term = term2;
        pat_tyvars = [];
        pat_vars = Sv.of_list1 s2.indices;}
    in
    match TMatch.try_match table system term1 pat2 with
    | `Match _ -> true
    | `FreeTyv | `NoMatch -> false


  (** remove any set which is subsumed by some other set. *)
  let mset_list_simplify table system (msets : Mset.t list) : Mset.t list =
    let rec clear_entailed before after =
      match after with
      | [] -> List.rev before
      | mset :: after ->
        let clear =
          List.exists (fun mset' ->
              mset_entail table system mset mset'
            ) (before @ after)
        in
        if clear then
          clear_entailed before after
        else
          clear_entailed (mset :: before) after
    in
    clear_entailed [] msets

  let mset_refresh env (mset : Mset.t) : Mset.t =
    let indices, subst = Term.refresh_vars `Global mset.indices in
    let msymb = Term.subst_isymb subst mset.msymb in
    Mset.mk env ~msymb ~indices

  let mset_subst env subst (mset : Mset.t) : Mset.t =
    let msymb = Term.subst_isymb subst mset.msymb in
    let indices = List.map (Term.subst_var subst) mset.indices in
    Mset.mk env ~msymb ~indices

  (** Compute the intersection of two msets *)
  let mset_inter table env (s1 : Mset.t) (s2 : Mset.t) : Mset.t option =
    let s1, s2 = mset_refresh env s1, mset_refresh env s2 in

    let tv = Vars.make_new Type.Timestamp "t" in
    let term1 = Term.Macro (s1.msymb, [], Term.Var tv) in
    let term2 = Term.Macro (s2.msymb, [], Term.Var tv) in

    let pat1 =
      { pat_term = term1;
        pat_tyvars = [];
        pat_vars = Sv.of_list1 s1.indices;}
    and pat2 =
      { pat_term = term2;
        pat_tyvars = [];
        pat_vars = Sv.of_list1 s2.indices;}
    in
    match TMatch.unify_opt table pat1 pat2 with
    | Some mv ->
      let subst = Mvar.to_subst ~mode:`Unif mv in
      let mset = mset_subst env subst s1 in
      assert (
        let mset' = mset_subst env subst s2 in
        mset = mset');
      Some mset
    | None -> None

  (** Intersets two list of [mset]s by doing:
      (∪ᵢ sᵢ) ∩ (∪ᵢ sᵢ) = ∪ᵢ,ⱼ (sᵢ∩sⱼ) *)
  let mset_list_inter
      (table : Symbols.table)
      (system : SystemExpr.t)
      (env : Sv.t)
      (mset_l1 : Mset.t list)
      (mset_l2 : Mset.t list) : Mset.t list
    =
    let mset_l =
      List.fold_left (fun acc mset1 ->
          List.fold_left (fun acc mset2 ->
              match mset_inter table env mset1 mset2 with
              | None -> acc
              | Some s -> s :: acc
            ) acc mset_l1
        ) [] mset_l2
    in
    mset_list_simplify table system mset_l

  let leq_tauto table (t : Term.timestamp) (t' : Term.timestamp) : bool =
    let rec leq t t' =
      match t,t' with
      | _ when t = t' -> true
      | Pred t, Pred t' -> leq t t'
      | Pred t,      t' -> leq t t'

      | Action (n,is), Action (n',is') ->
        Action.depends
          (Action.of_term n is table)
          (Action.of_term n' is' table)

      | _ -> false
    in
    leq t t'

  (*------------------------------------------------------------------*)
  (** [strenghten tbl system terms] strenghten [terms] by finding an inductive
      invariant on deducible messages which contains [terms]. *)
  let strengthen
      (table  : Symbols.table)
      (system : SystemExpr.t)
      (env    : Sv.t)
      (init_terms  : Term.messages) : msets
    =
    (** Return a specialization of [cand] that is a subset of [known]. *)
    let specialize
        (cand  : cand_set)
        (known : known_set) : cand_set option
      =
      let mv, c_pat = pat_of_cand_set cand
      and e_pat = pat_of_known_set known in

      match T.unify_opt ~mv table c_pat e_pat with
      | None -> None
      | Some mv ->
        (* check that [known.cond] holds *)
        let check_cond = match known.cond with
          | Term.Atom (`Timestamp (`Lt, t1, t2)) ->
            let subst = Mvar.to_subst ~mode:`Unif mv in
            let t1, t2 = Term.subst subst t1, Term.subst subst t2 in
            leq_tauto table t1 (Term.Pred t2)

          | Term.Fun (fs,_,_) when fs = Term.f_true -> true

          | _ -> assert false
        in

        if not check_cond then None
        else
          let mv =
            match known.tvar with
            | None -> mv
            | Some tv -> Mvar.remove (Vars.evar tv) mv
          in
          let cand =
            { term = cand.term;
              subst = mv;
              (* Note: variables must *not* be cleared yet,
                 because we must not forget the instantiation of any variable. *)
              indices = cand.indices @ known.indices; }
          in
          Some cand
    in

    (** In case [elem] is a sequence, return a specialization of [cand] that is
        a subset of [elem]'s elements. *)
    let specialize_from_seq
        (cand : cand_set)
        (elem : Term.message) : cand_set option
      =
      match elem with
      | Seq (is, elem) ->
        let is, s = Term.refresh_vars `Global is in
        let elem = Term.subst s elem in

        let known =
          { term    = elem;
            indices = is;
            tvar    = None;
            cond    = Term.mk_true; }
        in

        specialize cand known

      | _ -> None
    in

    (** Return a specialization of [cand] that is a subset of [term]. *)
    let specialize_from_term
        (cand : cand_set)
        (term : Term.message) : cand_set option
      =
      let term =
        { term    = term;
          indices = [];
          tvar    = None;
          cond    = Term.mk_true; }
      in

      specialize cand term
    in

    let specialize_all
        (cand : cand_set)
        (terms : Term.message list)
        (known_sets : known_sets) : cand_sets
      =
      let cands =
        List.fold_left (fun acc term ->
            specialize_from_seq  cand term ::
            specialize_from_term cand term ::
            acc
          ) [] terms
      in
      let cands =
        List.fold_left (fun acc known ->
            specialize cand known :: acc
          ) cands known_sets
      in
      List.concat_map (function
          | None -> []
          | Some x -> [x]
        ) cands
    in

    (** Return a list of speciablization of [cand] deducible from [terms] and
        [known].
        This includes both direct specialization, and specialization relying on
        the Function Application rule. *)
    let rec deduce
        (cand : cand_set)
        (terms : Term.message list)
        (known_sets : known_sets) : cand_sets
      =
      let direct_deds = specialize_all cand terms known_sets in
      let fa_deds = deduce_fa cand terms known_sets in

      direct_deds @ fa_deds

    (** Return a list of specialization of the tuples in [cand] deducible from
        [terms] and [pseqs]. *)
    and deduce_list
        (cand : cand_tuple_set)
        (terms : Term.messages)
        (known_sets : known_sets) : cand_tuple_sets
      =
      match cand.term with
      | [] -> [cand]
      | t :: tail ->
        (* find deducible speciablization of the first term of the tuple. *)
        let t_deds = deduce { cand with term = t } terms known_sets in

        (* for each such specialization, complete it into a specialization of
           the full tuple. *)
        List.concat_map (fun t_ded ->
            (* find a deducible speciablization of the tail of the tuple,
               starting from the  specialization of [t]. *)
            let cand_tail : cand_tuple_set = { t_ded with term = tail } in
            let tail_deds = deduce_list cand_tail terms known_sets in

            (* build the deducible specialization of the full tuple. *)
            List.map (fun (tail_ded : cand_tuple_set) ->
                { tail_ded with term = t_ded.term :: tail_ded.term }
              ) tail_deds
          ) t_deds

    (** Return a list of speciablization of [cand] deducible from [terms] and
        [pseqs] using Function Application.
        Does not include direct specialization. *)
    and deduce_fa
        (cand : cand_set)
        (terms : Term.messages)
        (known_sets : known_sets) : cand_sets
      =
      (* decompose the term using Function Application,
         find a deducible specialization of its tuple of arguments,
         and build the deducible speciablization of the initial term. *)
      match cand.term with
      (* special case for pure timestamps *)
      | _ as f when Term.is_pure_timestamp f -> [cand]

      (* special case for the if_then_else function symbol. *)
      | Term.Fun (fs, fty, [cond; t1; t2]) when fs = Term.f_ite ->

        (* then branch *)
        let f_terms_cand1 = { cand with term = [cond; t1] } in
        let f_terms_deds1 = deduce_list f_terms_cand1 terms known_sets in

        (* else branch *)
        let f_terms_cand2 = { cand with term = [cond; t2] } in
        let f_terms_deds2 = deduce_list f_terms_cand2 terms known_sets in

        (* union of terms deducible from both branch *)
        let f_terms_deds = f_terms_deds1 @ f_terms_deds2 in

        List.map (fun (f_terms_ded : cand_tuple_set) ->
            { f_terms_ded with
              term = Term.Fun (fs, fty, f_terms_ded.term) }
          ) f_terms_deds

      | Term.Fun (fs, fty, f_terms) ->
        let f_terms_cand = { cand with term = f_terms } in
        let f_terms_deds = deduce_list f_terms_cand terms known_sets in
        List.map (fun (f_terms_ded : cand_tuple_set) ->
            { f_terms_ded with
              term = Term.Fun (fs, fty, f_terms_ded.term) }
          ) f_terms_deds

      (* similar to the [Fun _] case *)
      | Term.Atom (`Message (ord, t1, t2)) ->
        let f_terms_cand = { cand with term = [t1;t2] } in
        let f_terms_deds = deduce_list f_terms_cand terms known_sets in
        List.map (fun (f_terms_ded : cand_tuple_set) ->
            let t1, t2 = Utils.as_seq2 f_terms_ded.term in
            { f_terms_ded with
              term = Term.Atom (`Message (ord, t1, t2)) }
          ) f_terms_deds

      | _ -> []
    in

    (** Retrun a list of specialization of [cand] deducible from
        [terms, known_sets] for action [a] at time [a]. *)
    let filter_deduce_action
        (a : Symbols.action Symbols.t)
        (cand : Mset.t)
        (terms : Term.message list)
        (known_sets : Term.timestamp -> known_sets) : Mset.t list
      =
      (* we create the timestamp at which we are *)
      let i = Action.arity a table in
      let is = List.init i (fun _ -> Vars.make_new Type.Index "i") in
      let ts = Term.Action (a, is) in

      (* we unroll the definition of [cand] at time [ts] *)
      let cntxt = Constr.{ system; table; models = None; } in
      match Macros.get_definition_opt cntxt cand.msymb ts with
      | None -> []

      | Some body ->
        let cand_set = {
          term = body;
          indices = cand.indices @ is;
          subst = Mvar.empty; }
        in
        (* we instantiated the known terms at time [ts] *)
        let known_sets = known_sets ts in
        let ded_sets = deduce cand_set terms known_sets in

        let mset_l =
          List.fold_left (fun msets ded_set ->
              let subst = Mvar.to_subst ~mode:`Unif ded_set.subst in
              let msymb = Term.subst_isymb subst cand.msymb in
              let indices = List.map (Term.subst_var subst) cand.indices in
              let mset = Mset.mk env ~msymb ~indices in
              mset :: msets
            ) [] ded_sets
        in
        mset_list_simplify table system mset_l
    in

    let filter_deduce_action_list
        (a : Symbols.action Symbols.t)
        (cands : msets)
        (terms : Term.message list)
        (known_sets : Term.timestamp -> known_sets) : msets
      =
      let msets =
        List.map (fun (mname, cand_l) ->
            let mset_l =
              List.concat_map (fun cand ->
                  filter_deduce_action a cand terms known_sets
                ) cand_l
            in
            (mname, mset_list_inter table system env cand_l mset_l)
          ) cands
      in
      msets
    in

    let filter_deduce_all_actions0
        (cands : msets)
        (terms : Term.message list)
        (known_sets : Term.timestamp -> known_sets) : msets
      =
      (* FIXME: dont compute the full description map, just the name map *)
      (* let descrs = SystemExpr.symbs ~with_dummies:false tbl system in *)
      let descrs = SystemExpr.map_descrs table system (fun x -> x) in
      List.fold_left (fun cands descr ->
          let name = descr.Action.name in
          filter_deduce_action_list name cands terms known_sets
        ) cands descrs
    in

    let filter_deduce_all_actions
        (cands : msets)
        (terms : Term.message list)
        (known : msets) : msets
      =
      let known : Mset.t list = msets_to_list known in

      let known_sets (ts' : Term.timestamp) =
        List.map (fun (mset : Mset.t) ->
          let tv = Vars.make_new Type.Timestamp "t" in
          let term = Term.Macro (mset.msymb, [], Var tv) in
          { term = term;
            indices = mset.indices;
            tvar = Some tv;
            cond = Term.mk_atom `Lt (Term.Var tv) ts'; }
        ) known
      in
      filter_deduce_all_actions0 cands terms known_sets
    in

    let rec deduce_fixpoint
        (cands : msets)
        (terms : Term.message list) : msets
      =
      let cands' = filter_deduce_all_actions cands terms cands in

      (* REM *)
      (* Fmt.epr "next:@.@[<v>%a@]@." pp_msets cands'; *)

      (* check if [cands] is included in [cands'] *)
      if List.for_all (fun (mname, cand_l) ->
          let cand_l' = List.assoc_opt mname cands' in
          let cand_l' = odflt [] cand_l' in

          List.for_all (fun cand ->
              List.exists (fun cand' ->
                  mset_entail table system cand cand'
                ) cand_l'
            ) cand_l
        ) cands
      then cands'
      else deduce_fixpoint cands' terms
    in

    let init_fixpoint : msets =
      Symbols.Macro.fold (fun mn def _ msets ->
          let ty, indices = match def with
            | Symbols.Global (i, ty)
            | Symbols.State (i, ty) ->
              ty, List.init i (fun _ -> Vars.make_new Type.Index "i")

            | Symbols.Input | Symbols.Output | Symbols.Frame ->
              Type.Message, []

            | Symbols.Cond | Symbols.Exec ->
              Type.Boolean, []
          in
          let ms = Term.mk_isymb mn ty indices in
          let mset = Mset.mk env ~msymb:ms ~indices in
          msets_add mset msets
        ) [] table
    in

    (* REM *)
    (* Fmt.epr "init_fp:@.@[<v>%a@]@." pp_msets init_fixpoint; *)

    deduce_fixpoint init_fixpoint init_terms

  (*------------------------------------------------------------------*)
  let unify ?mv table t1 t2  = `NoMgu      (* TODO *)

  let unify_opt ?mv table t1 t2 =
    match unify ?mv table t1 t2 with
    | `Freetyv | `NoMgu -> None
    | `Mgu mv -> Some mv

  (*------------------------------------------------------------------*)
  let try_match
      ?mv
      ?(mode=`Eq)
      (table : Symbols.table)
      (system : SystemExpr.t)
      (t : t)
      (p : t pat)
    : [ `FreeTyv | `NoMatch | `Match of Mvar.t ]
    =
    let exception NoMatch in

    (* [ty_env] must be closed at the end of the matching *)
    let ty_env = Type.Infer.mk_env () in
    let univars, ty_subst  = Type.Infer.open_tvars ty_env p.pat_tyvars in
    let pat = Equiv.tsubst ty_subst p.pat_term in

    (* substitute back the univars by the corresponding tvars *)
    let ty_subst_rev =
      List.fold_left2 (fun s tv tu ->
          Type.tsubst_add_univar s tu (Type.TVar tv)
        ) Type.tsubst_empty p.pat_tyvars univars
    in

    let support = Sv.map (Vars.tsubst_e ty_subst) p.pat_vars in
    let env = Sv.diff (Sv.union (Equiv.fv t) (Equiv.fv pat)) support in

    let flip = function
      | `Eq        -> `Eq
      | `Covar     -> `Contravar
      | `Contravar -> `Covar
    in

    let term_match_opt : type a b.
        ?vars:Sv.t ->
        a Term.term ->
        b Term.term ->
        match_state ->
        match_state option
      = fun ?(vars=Sv.empty) term elem st ->
      let pat =
        Term.{ pat_tyvars = [];
               pat_vars = Sv.union vars p.pat_vars;
               pat_term = elem; }
      in
      match TMatch.try_match_term ~mv:st.mv table system term pat with
      | `Match mv -> Some { st with mv }
      | `FreeTyv | `NoMatch -> None
    in

    let term_match ?vars term pat st : match_state =
      match term_match_opt ?vars term pat st with
      | None -> raise NoMatch
      | Some st -> st
    in

    (*------------------------------------------------------------------*)
    (** In case [pat] is a sequence, try to match [term] as an element
        of [pat]. *)
    let seq_mem_one
        (term : Term.message)
        (elem : Term.message)
        (st   : match_state) : match_state option
      =
      match elem with
      | Seq (is, elem) ->
        let is, s = Term.refresh_vars `Global is in
        let elem = Term.subst s elem in

        let is_s = Sv.of_list1 is in

        begin
            match term_match_opt ~vars:is_s term elem st with
            | None -> None
            | Some st ->
              let mv = Mvar.filter (fun v _ -> not (Sv.mem v is_s)) st.mv in
              Some { st with mv }
        end

      | _ -> None
    in

    (** Try to match [term] as an element of a sequence in [elems]. *)
    let seq_mem
        (term  : Term.message)
        (elems : Term.message list)
        (st    : match_state) : match_state option
      =
      List.find_map (fun elem -> seq_mem_one term elem st) elems
    in

    (*------------------------------------------------------------------*)
    (** Try to match [term] as an element the mset [mset]. *)
    let mset_mem_one
        (term : Term.message)
        (mset : Mset.t)
        (st   : match_state) : match_state option
      =
      let tv = Vars.make_new Type.Timestamp "t" in
      let pat = Term.Macro (mset.msymb, [], Term.Var tv) in

      let vars = Sv.add (Vars.EVar tv) (Sv.of_list1 mset.indices) in

      match term_match_opt ~vars term pat st with
      | None -> None
      | Some st ->
        let mv = Mvar.filter (fun v _ -> not (Sv.mem v vars)) st.mv in
        Some { st with mv }
    in

    (** Try to match [term] as an element of [msets]. *)
    let mset_mem
        (term   : Term.message)
        (mset_l : Mset.t list)
        (st     : match_state) : match_state option
      =
      List.find_map (fun elem -> mset_mem_one term elem st) mset_l
    in

    (*------------------------------------------------------------------*)
    (** Duplicate checking: see [Action.is_dup_match] *)
    let is_dup
        (term  : Term.message)
        (elems : Term.message list)
        (st    : match_state) : match_state option
      =
      let eterm_match (Term.ETerm t1) (Term.ETerm t2) st =
        term_match_opt t1 t2 st
      in

      Action.is_dup_match eterm_match st table term elems
    in

    (*------------------------------------------------------------------*)
    (** Check that [term] can be deduced from [pat_terms].
        This check is modulo:
        - Restr: all elements may not be used;
        - Sequence expantion: sequences may be expanded;
        - Function Application: [term] may be decomposed into smaller terms. *)
    let rec match_term_incl
        (term      : Term.message)
        (pat_terms : Term.message list)
        (mset_l    : Mset.t list)
        (st        : match_state) : match_state
      =
      match is_dup term pat_terms st with
      | Some st -> st
      | None ->
        match seq_mem term pat_terms st with
        | Some st -> st
        | None ->
          match mset_mem term mset_l st with
          | Some st -> st
          | None ->
            (* if that fails, decompose [term] through the Function Application
               rule, and recurse. *)
            match term with
            | Term.Fun (_, _, terms) ->
              List.fold_left (fun st term ->
                  match_term_incl term pat_terms mset_l st
                ) st terms

            | Term.Atom (`Message (_, t1, t2)) ->
              List.fold_left (fun st term ->
                  match_term_incl term pat_terms mset_l st
                ) st [t1; t2]

            | Term.Seq (is, term) ->
              let is, subst = Term.refresh_vars `Global is in
              let term = Term.subst subst term in

              let st = { st with bvs = Sv.add_list st.bvs is; } in
              match_term_incl term pat_terms mset_l st

            | Term.Exists (es, term)
            | Term.ForAll (es, term)
              when List.for_all (fun (Vars.EVar v) ->
                  let k = Vars.kind v in
                  Type.equalk k Type.KIndex || Type.equalk k Type.KTimestamp
                ) es
              ->
              let es, subst = Term.erefresh_vars `Global es in
              let term = Term.subst subst term in

              let st = { st with bvs = Sv.union st.bvs (Sv.of_list es); } in
              match_term_incl term pat_terms mset_l st

            | Find (is, c, d, e) ->
              let is, subst = Term.refresh_vars `Global is in
              let c, d = Term.subst subst c, Term.subst subst d in

              let st1 = { st with bvs = Sv.add_list st.bvs is; } in

              let st1 =
                match_term_incl c pat_terms mset_l st1 |>
                match_term_incl d pat_terms mset_l
              in
              match_term_incl d pat_terms mset_l { st1 with bvs = st.bvs }

            | _ -> raise NoMatch
    in

    (*------------------------------------------------------------------*)
    (** Greedily check entailment through an inclusion check of [terms] in
        [pat_terms]. *)
    let match_equiv_incl
        (terms     : Term.message list)
        (pat_terms : Term.message list)
        (st        : match_state) : match_state
      =
      let msets = strengthen table system env pat_terms in
      let mset_l = msets_to_list msets in

      (* REM *)
      (* Fmt.epr "final result:@.@[<v>%a@]@." pp_msets msets; *)

      List.fold_left (fun st term ->
          match_term_incl term pat_terms mset_l st
        ) st terms
    in

    (*------------------------------------------------------------------*)
    let rec match_equiv_eq
        (terms     : Term.message list)
        (pat_terms : Term.message list)
        (st        : match_state) : match_state
      =
      if List.length terms <> List.length pat_terms then raise NoMatch;

      List.fold_right2 term_match terms pat_terms st
    in

    (*------------------------------------------------------------------*)
    (** Check entailment between two equivalences.
        - [Covar]    : [pat_es] entails [es]
        - [Contravar]: [es] entails [pat_es] *)
    let tmatch_e
        ~(mode     : [`Eq | `Covar | `Contravar])
         (terms     : Term.messages)
         (pat_terms : Term.messages)
         (st        : match_state)
      : match_state =
      match mode with
      | `Eq        -> match_equiv_eq terms pat_terms st
      | `Contravar -> match_equiv_eq terms pat_terms st
      (* FIXME: in contravariant position, we cannot check for inclusion
         because, in the seq case, this requires to infer the seq
         variables for the *term* being matched. Consequently, this is no longer
         a matching problem, but is a unification problem. *)

      | `Covar     -> match_equiv_incl terms pat_terms st
    in

    let rec fmatch ~mode (t : Equiv.form) (pat : Equiv.form) (st : match_state)
      : match_state =
      match t, pat with
      | Impl (t1, t2), Impl (pat1, pat2) ->
        let st = fmatch ~mode:(flip mode) t1 pat1 st in
        fmatch ~mode t2 pat2 st

      | Atom (Reach t), Atom (Reach pat) ->
        term_match t pat st

      | Atom (Equiv es), Atom (Equiv pat_es) ->
        tmatch_e ~mode es pat_es st

      | Quant (q,es,t), Quant (q',es',t') ->
        (* TODO: match under binders (see Term.ml)  *)
        if q = q' && es = es' && t = t'
        then st
        else raise NoMatch

      | _ -> raise NoMatch
    in

    let mv_init = odflt Mv.empty mv in
    let st_init : match_state =
      { bvs = Sv.empty; mv = mv_init; table; system; support; env; }
    in
    let mode = match mode with
      | `Eq -> `Eq
      | `EntailRL -> `Covar
      | `EntailLR -> `Contravar
    in

    try
      let st = fmatch ~mode t pat st_init in

      if not (Type.Infer.is_closed ty_env)
      then `FreeTyv
      else
        let mv =
          Mvar.fold (fun (Vars.EVar v) t mv ->
              let v = Vars.tsubst ty_subst_rev v in
              Mvar.add (Vars.EVar v) t mv
            ) st.mv Mvar.empty
        in
        `Match mv

    with NoMatch -> `NoMatch


  (*------------------------------------------------------------------*)
  let rec find_map :
    type b.
    many:bool ->
    Symbols.table ->
    SystemExpr.t ->
    Vars.env ->
    t -> b Term.term pat ->
    (b Term.term -> Vars.evars -> Mvar.t -> b Term.term) ->
    t option
    = fun ~many table system env (e : Equiv.form) p func ->
      match e with
      | Atom (Reach f) ->
        omap
          (fun x -> Equiv.Atom (Reach (x)))
          (TMatch.find_map ~many table system env f p func)
      | Atom (Equiv e) ->
        let found = ref false in

        let e = List.fold_left (fun acc f ->
            if not !found || many then
              match TMatch.find_map ~many table system env f p func with
              | None -> f :: acc
              | Some f -> found := true; f :: acc
            else f :: acc
          ) [] e
        in
        let e = List.rev e in

        if !found then Some (Atom (Equiv e)) else None

      | Impl (e1, e2) ->
        let found, e1 =
          match find_map ~many table system env e1 p func with
          | Some e1 -> true, e1
          | None -> false, e1
        in

        let found, e2 =
          if not found || many then
            match find_map ~many table system env e2 p func with
            | Some e2 -> true, e2
            | None -> false, e2
          else found, e2
        in
        if found then Some (Impl (e1, e2)) else None

      | Quant _ -> None  (* FIXME: match under binders *)

end
