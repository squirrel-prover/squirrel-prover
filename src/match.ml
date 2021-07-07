open Utils
open Term

module Sv = Vars.Sv
module Mv = Vars.Mv

let dbg ?(force=false) s =
  if force then Printer.prt `Dbg s
  else Printer.prt `Ignore s

(*------------------------------------------------------------------*)
(** {2 Patterns} *)

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
(** {2 Matching variable assignment} *)

module Mvar : sig
  type t

  val make : eterm Mv.t -> t

  val empty : t

  val union : t -> t -> t

  val add : Vars.evar -> eterm -> t -> t

  val remove : Vars.evar -> t -> t 

  val mem : Vars.evar -> t -> bool
    
  val find : Vars.evar -> t -> eterm

  val is_empty : t -> bool

  val filter : (Vars.evar -> eterm -> bool) -> t -> t

  val fold : (Vars.evar -> eterm -> 'b -> 'b) -> t -> 'b -> 'b

  val to_subst : mode:[`Match|`Unif] -> t -> subst 

end = struct
  (** [id] is a unique identifier used to do memoisation. *)
  type t = { id    : int;
             subst : eterm Mv.t; }

  let cpt = ref 0
  let make subst = { id = (incr cpt; !cpt); subst }

  let empty = make (Mv.empty)

  let union mv1 mv2 = 
    make (Mv.union (fun _ _ _ -> assert false) mv1.subst mv2.subst)

  let add (v : Vars.evar) (t : eterm) (m : t) : t = 
    make (Mv.add v t m.subst)

  let remove (v : Vars.evar) (m : t) : t = 
    make (Mv.remove v m.subst)

  let mem (v : Vars.evar) (m : t) : bool = Mv.mem v m.subst

  let find (v : Vars.evar) (m : t) = Mv.find v m.subst

  let is_empty (m : t) = Mv.is_empty m.subst

  let filter f (m : t) : t = make (Mv.filter f m.subst)

  let fold f (m : t) (init : 'b) : 'b = Mv.fold f m.subst init

  let to_subst ~(mode:[`Match|`Unif]) (mv : t) : subst =   
    let s =
      Mv.fold (fun v t subst ->
          match v, t with
          | Vars.EVar v, ETerm t ->
            ESubst (mk_var v, cast (Vars.kind v) t) :: subst
        ) mv.subst []
    in

    match mode with
    | `Match -> s
    | `Unif ->
      (* We need to substitute until we reach a fixpoint *)
      let support = Mv.fold (fun v _ supp -> Sv.add v supp) mv.subst Sv.empty in
      let rec fp_subst t =
        if Sv.disjoint (fv t) support then t
        else fp_subst (subst s t)
      in
      List.map (fun (ESubst (v, t)) -> ESubst (v, fp_subst t)) s

  
  (* with memoisation *)
  let to_subst =
    let module H1 = struct
      type _t = t
      type t = _t
      let hash t = t.id
      let equal t t' = t.id = t'.id
    end in 
    let module H2 = struct
      type t = [`Match|`Unif]
      let hash = function `Match -> 1 | `Unif -> 0
      let equal x y = x == y
    end in 
    let module Memo = Ephemeron.K2.Make (H1) (H2) in
    let memo = Memo.create 256 in
    fun ~mode t ->
      try Memo.find memo (t,mode) with
      | Not_found -> 
        let r = to_subst ~mode t in
        Memo.add memo (t,mode) r;
        r

end


(*------------------------------------------------------------------*)
(** {2 Matching information for error messages} *)

let minfos_ok : type a. a term -> match_infos -> match_infos =
  fun term minfos ->
  Mt.add (Term.ETerm term) MR_ok minfos

let minfos_failed : type a. a term -> match_infos -> match_infos =
  fun term minfos ->
  Mt.add (Term.ETerm term) MR_failed minfos

let minfos_check_st : type a. 
  a term -> message list -> match_infos -> match_infos 
  =
  fun term subterms minfos ->
  Mt.add (Term.ETerm term) (MR_check_st subterms) minfos   

(*------------------------------------------------------------------*)
(** Normalize a match information map, by making a term tagged 
    [MR_check_st] only if:
    -     at least one of its subterms is tagged [MR_ok] 
    - and at least one of its subterms is tagged [MR_fail]. *)
let minfos_norm (minit : match_infos) : match_infos =
  let rec norm (ETerm t as et) mfinal : match_info * match_infos =
    if Mt.mem et mfinal 
    then Mt.find et mfinal, mfinal
    else match Mt.find et minit with
      | MR_ok | MR_failed as r -> r, Mt.add et r mfinal
      | MR_check_st st -> 
        let infos, mfinal = 
          List.fold_left (fun (infos, mfinal) t ->
              let i, mfinal = norm (ETerm t) mfinal in
              i :: infos, mfinal
            ) ([], mfinal) st
        in
        (* special case for binders, because alpha-renamed subterms
           cannot be checked later *)
        if List.for_all (fun x -> x = MR_ok) infos
        then MR_ok, Mt.add et MR_ok mfinal
        else if Term.is_binder t
        then MR_failed, Mt.add et MR_failed mfinal
        else MR_check_st st, Mt.add et (MR_check_st st) mfinal
  in

  Mt.fold (fun et _ mfinal -> 
      let _, mfinal = norm et mfinal in
      mfinal) minit Mt.empty

(*------------------------------------------------------------------*)
exception NoMatch of (message list * match_infos) option

let no_match ?infos () = raise (NoMatch infos)   

(*------------------------------------------------------------------*)
(** {2 Matching and unification internal states} *)

(** (Descending) state used in the matching algorithm. *)
type match_state = {
  mv  : Mvar.t;          (** inferred variable assignment *)
  bvs : Sv.t;            (** bound variables "above" the current position *)

  support  : Sv.t;       (** free variable which we are trying to match *)
  env      : Sv.t;       (** rigid free variables (disjoint from [support]) *)

  ty_env   : Type.Infer.env;
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

  ty_env   : Type.Infer.env;
  table    : Symbols.table;
}

(*------------------------------------------------------------------*)
(** {2 Module signature of matching} *)

type match_res = 
  | FreeTyv
  | NoMatch of (messages * match_infos) option 
  | Match   of Mvar.t

type f_map =
  eterm -> Vars.evars -> Term.message list -> [`Map of eterm | `Continue] 

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
    match_res

  val try_match_term :
    ?mv:Mvar.t ->
    ?mode:[`Eq | `EntailLR | `EntailRL] ->
    Symbols.table ->
    SystemExpr.t ->
    'a term -> 'b term pat ->
    match_res

  val map : f_map -> Vars.env -> t -> t option
end

(*------------------------------------------------------------------*)
(** {2 Matching and unification} *)

(*------------------------------------------------------------------*)
(** {3 Term matching and unification} *)

module T (* : S with type t = message *) = struct
  type t = message

  let pp_pat pp_t fmt p =
    Fmt.pf fmt "@[<hov 0>{term = @[%a@];@ tyvars = @[%a@];@ vars = @[%a@]}@]"
      pp_t p.pat_term
      (Fmt.list ~sep:Fmt.sp Type.pp_tvar) p.pat_tyvars
      (Fmt.list ~sep:Fmt.sp Vars.pp_e) (Sv.elements p.pat_vars)

  (*------------------------------------------------------------------*)
  exception NoMgu 
    
  (* Invariants:
     - [st.mv] supports in included in [support].
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
          if Type.Infer.unify_eq st.ty_env ty ty' = `Fail then
            raise NoMgu;
      ) vs vs';

    (* refresh [vs] *)
    let vs, s = erefresh_vars `Global vs in

    (* refresh [vs'] using the same renaming *)
    let s' = List.map2 (fun (ESubst (_, new_v)) (Vars.EVar v') ->
        match Type.equal_w (ty new_v) (Vars.ty v') with
        | None -> assert false
        | Some Type.Type_eq -> ESubst (mk_var v', new_v)
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
          v', mk_var v
        else if not (Sv.mem (Vars.evar v') st.support) then
          v, t
        else if Vars.compare v v' < 0 then
          v, t
        else
          v', mk_var v

      | _ -> v, t
    in
    let ev = Vars.EVar v in

    if not (Sv.mem ev st.support)
    then if t = mk_var v then st.mv else raise NoMgu

    else (* [v] in the support, and [v] smaller than [v'] if [t = Var v'] *)
      match Mvar.find ev st.mv with
      (* first time we see [v]: store the substitution and add the
         type information. *)
      | exception Not_found ->
        if Type.Infer.unify_eq st.ty_env (ty t) (Vars.ty v) = `Fail then
          raise NoMgu;

        (* check that we are not trying to unify [v] with a term using
           bound variables. *)
        if not (Sv.disjoint (fv t) st.bvs) then raise NoMgu;

        (Mvar.add ev (ETerm t) st.mv)

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
      unif_l [mk_var t1; mk_var t2] [mk_var t1'; mk_var t2'] st

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
        vunif (mk_var i) i' { st with mv }
      ) st.mv is is'

  (*------------------------------------------------------------------*)
  (** Exported *)
  let unify
      ?mv:mv
      (table : Symbols.table)
      (t1 : t pat)
      (t2 : t pat) : [`FreeTyv | `NoMgu | `Mgu of Mvar.t]
    =
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

    let mv_init = odflt Mvar.empty mv in
    let st_init = {
      subst_vs = Sv.empty; bvs = Sv.empty; mv = mv_init ;
      support; env; ty_env; table; } 
    in

    try
      let mv = unif term1 term2 st_init in

      if not (Type.Infer.is_closed ty_env)
      then `FreeTyv
      else
        let mv =
          Mvar.fold (fun (Vars.EVar v) t mv ->
              let v = Vars.tsubst ty_subst_rev v in
              Mvar.add (Vars.EVar v) t mv
            ) mv Mvar.empty
        in
        `Mgu mv

    with NoMgu -> `NoMgu


  (*------------------------------------------------------------------*)
  (** Exported *)
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
        | exception Uncastable -> no_match ()
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

    | _, _ -> no_match ()

  (* Return: left subst, right subst, match state *)
  and match_bnds (vs : Vars.evars) (vs' : Vars.evars) st :
    esubst list * esubst list * match_state =
    if List.length vs <> List.length vs' then
      no_match ();

    (* check that types are compatible *)
    List.iter2 (fun (Vars.EVar v) (Vars.EVar v') ->
        let ty, ty' = Vars.ty v, Vars.ty v' in
        match Type.equal_w ty ty' with
        | None -> no_match ()
        | Some Type.Type_eq ->
          if Type.Infer.unify_eq st.ty_env ty ty' = `Fail then
            no_match ();
      ) vs vs';

    (* refresh [vs] *)
    let vs, s = erefresh_vars `Global vs in

    (* refresh [vs'] using the same renaming *)
    let s' = List.map2 (fun (ESubst (_, new_v)) (Vars.EVar v') ->
        match Type.equal_w (ty new_v) (Vars.ty v') with
        | None -> assert false
        | Some Type.Type_eq -> ESubst (mk_var v', new_v)
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
    if fn <> fn' then no_match ();

    List.fold_left2 (fun mv i i' -> 
        vmatch (mk_var i) i' { st with mv }
      ) st.mv is is'


  (* Match a variable of the pattern with a term. *)
  and vmatch : type a. a term -> a Vars.var -> match_state -> Mvar.t =
    fun t v st ->
    let ev = Vars.EVar v in

    if not (Sv.mem ev st.support)
    then (* [v] not in the pattern *)
      if t = mk_var v then st.mv else no_match () 

    else (* [v] in the pattern *)
      match Mvar.find ev st.mv with
      (* If this is the first time we see the variable, store the subterm
         and add the type information. *)
      | exception Not_found ->
        if Type.Infer.unify_eq st.ty_env (ty t) (Vars.ty v) = `Fail then
          no_match ();

        (* check that we are not trying to match [v] with a term free bound
           variables. *)
        if not (Sv.disjoint (fv t) st.bvs) then no_match ();

        Mvar.add ev (ETerm t) st.mv 

      (* If we already saw the variable, check that the subterms are
         identical. *)
      | ETerm t' -> match cast (kind t) t' with
        | exception Uncastable -> no_match ()
        (* TODO: alpha-equivalent *)
        | t' -> if t <> t' then no_match () else st.mv

  (* matches an atom *)
  and atmatch (at : generic_atom) (at' : generic_atom) st : Mvar.t =
    match at, at' with
    | `Message (ord, t1, t2), `Message (ord', t1', t2') ->
      if ord <> ord' then no_match ();
      tmatch_l [t1;t2] [t1';t2'] st

    | `Timestamp (ord, t1, t2), `Timestamp (ord', t1', t2') ->
      if ord <> ord' then no_match ();
      tmatch_l [t1;t2] [t1';t2'] st

    | `Index (ord, t1, t2), `Index (ord', t1', t2') ->
      if ord <> ord' then no_match ();
      tmatch_l [mk_var t1; mk_var t2] [mk_var t1'; mk_var t2'] st

    | `Happens ts, `Happens ts' -> tmatch ts ts' st

    | _, _ -> no_match ()

  (*------------------------------------------------------------------*)
  (** Exported *)
  let try_match_term : type a b.
    ?mv:Mvar.t ->
    ?mode:[`Eq | `EntailLR | `EntailRL] ->
    Symbols.table ->
    SystemExpr.t ->
    a term -> b term pat -> 
    match_res
    =
    fun ?mv ?mode table system t p ->

    (* Term matching ignores [mode]. Matching in [Equiv] does not. *)

    (* [ty_env] must be closed at the end of the matching *)
    let ty_env = Type.Infer.mk_env () in
    let univars, ty_subst = Type.Infer.open_tvars ty_env p.pat_tyvars in
    let pat = tsubst ty_subst p.pat_term in

    (* substitute back the univars by the corresponding tvars *)
    let ty_subst_rev =
      List.fold_left2 (fun s tv tu ->
          Type.tsubst_add_univar s tu (Type.TVar tv)
        ) Type.tsubst_empty p.pat_tyvars univars
    in

    let support = Sv.map (Vars.tsubst_e ty_subst) p.pat_vars in
    let env = Sv.diff (Sv.union (Term.fv t) (Term.fv pat)) support in

    let mv_init = odflt Mvar.empty mv in
    let st_init : match_state =
      { bvs = Sv.empty; mv = mv_init; table; system; env; support; ty_env;}
    in

    try
      let mv = tmatch t pat st_init in

      if not (Type.Infer.is_closed ty_env)
      then FreeTyv
      else
        let mv =
          Mvar.fold (fun (Vars.EVar v) t mv ->
              let v = Vars.tsubst ty_subst_rev v in
              Mvar.add (Vars.EVar v) t mv
            ) mv Mvar.empty
        in
        Match mv

    with 
    | NoMatch minfos -> NoMatch minfos

  let try_match = try_match_term 

  let _map : type a.
    f_map ->
    Vars.env ->
    vars:Vars.evars ->
    conds:Term.message list ->
    a term -> bool * a term
    =
    fun func env ~vars ~conds t ->
    
    (* the return boolean indicates whether a match was found in the subterm. *)
    let rec map : type a.
      Vars.env ->
      Vars.evars ->
      Term.message list -> 
      a term ->
      bool * a term
      =
      fun env vars conds t ->
        match func (ETerm t) vars conds with
        (* head matches *)
        | `Map (ETerm t') ->
          true, cast (kind t) t'

        (* head does not match, recurse with a special handling of binders and if *)
        | `Continue ->
          match t with
          | ForAll (vs, b) ->
            let env, vs, s = erefresh_vars_env env vs in
            let b = Term.subst s b in
            let vars = List.rev_append vs vars in
            let found, b = map env vars conds b in
            let t' = Term.mk_forall ~simpl:false vs b in

            if found then true, t' else false, t

          | Exists (vs, b) ->
            let env, vs, s = erefresh_vars_env env vs in
            let b = Term.subst s b in
            let vars = List.rev_append vs vars in
            let found, b = map env vars conds b in
            let t' = Term.mk_exists ~simpl:false vs b in

            if found then true, t' else false, t

          | Find (b, c, d, e) ->
            let env1, vs, s = refresh_vars_env env b in
            let c, d = Term.subst s c, Term.subst s d in
            let vars1 = List.rev_append (List.map Vars.evar b) vars in
            let dconds = c :: conds in
            let found0, c = map env1 vars1 conds  c in
            let found1, d = map env1 vars1 dconds d in
            let found2, e = map env   vars  conds  e in
            let t' = Term.mk_find b c d e in
            let found = found0 || found1 || found2 in

            if found then true, t' else false, t

          | Seq (vs, b) ->
            let env, vs, s = refresh_vars_env env vs in
            let b = Term.subst s b in
            let vars = List.rev_append (List.map Vars.evar vs) vars in
            let found, b = map env vars conds b in
            let t' = Term.mk_seq0 vs b in

            if found then true, t' else false, t

          | Term.Fun (fs, _, [c;ft;fe]) when fs = Term.f_ite ->            
            let tconds = c :: conds in
            let econds = Term.mk_not ~simpl:false c :: conds in
            let found0, c  = map env vars conds  c in
            let found1, ft = map env vars tconds ft in
            let found2, fe = map env vars econds fe in
            let t' = Term.mk_ite ~simpl:false c ft fe in
            let found = found0 || found1 || found2 in

            if found then true, t' else false, t

          | _ ->
            tmap_fold (fun found (ETerm t) ->
                let found', t = map env vars conds t in
                found || found', Term.ETerm t
              ) false t
    in

    map env vars conds t 
                 
  (** Exported *)
  let map : type a. f_map -> Vars.env -> a term -> a term option
    =
    fun func env t ->
    let found, t = _map func env ~vars:[] ~conds:[] t in
    match found with
    | false -> None
    | true  -> Some t
end

(*------------------------------------------------------------------*)
(** {3 Equiv matching and unification} *)


module E : S with type t = Equiv.form = struct
  (* We include Term.Match, and redefine any necessary function *)
  include T

  type t = Equiv.form

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
    let term1 = Term.mk_macro s1.msymb [] (Term.mk_var tv) in
    let term2 = Term.mk_macro s2.msymb [] (Term.mk_var tv) in

    let pat2 =
      { pat_term = term2;
        pat_tyvars = [];
        pat_vars = Sv.of_list1 s2.indices;}
    in
    match T.try_match table system term1 pat2 with
    | Match _ -> true
    | FreeTyv | NoMatch _ -> false


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
    let term1 = Term.mk_macro s1.msymb [] (Term.mk_var tv) in
    let term2 = Term.mk_macro s2.msymb [] (Term.mk_var tv) in

    let pat1 =
      { pat_term = term1;
        pat_tyvars = [];
        pat_vars = Sv.of_list1 s1.indices;}
    and pat2 =
      { pat_term = term2;
        pat_tyvars = [];
        pat_vars = Sv.of_list1 s2.indices;}
    in
    match T.unify_opt table pat1 pat2 with
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
            leq_tauto table t1 (Term.mk_pred t2)

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
              term = Term.mk_fun0 fs fty (f_terms_ded.term) }
          ) f_terms_deds

      | Term.Fun (fs, fty, f_terms) ->
        let f_terms_cand = { cand with term = f_terms } in
        let f_terms_deds = deduce_list f_terms_cand terms known_sets in
        List.map (fun (f_terms_ded : cand_tuple_set) ->
            { f_terms_ded with
              term = Term.mk_fun0 fs fty (f_terms_ded.term) }
          ) f_terms_deds

      (* similar to the [Fun _] case *)
      | Term.Atom (`Message (ord, t1, t2)) ->
        let f_terms_cand = { cand with term = [t1;t2] } in
        let f_terms_deds = deduce_list f_terms_cand terms known_sets in
        List.map (fun (f_terms_ded : cand_tuple_set) ->
            let t1, t2 = Utils.as_seq2 f_terms_ded.term in
            { f_terms_ded with
              term = Term.mk_atom (ord :> Term.ord) t1 t2 }
          ) f_terms_deds

      | _ -> []
    in

    (** Return a list of specialization of [cand] deducible from
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
      let ts = Term.mk_action a is in

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
      let names = SystemExpr.symbs ~with_dummies:false table system in
      System.Msh.fold (fun _ name cands ->
          filter_deduce_action_list name cands terms known_sets
        ) names cands
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
          let term = Term.mk_macro mset.msymb [] (Term.mk_var tv) in
          { term = term;
            indices = mset.indices;
            tvar = Some tv;
            cond = Term.mk_atom `Lt (Term.mk_var tv) ts'; }
        ) known
      in
      filter_deduce_all_actions0 cands terms known_sets
    in

    let rec deduce_fixpoint
        (cands : msets)
        (terms : Term.message list) : msets
      =
      let cands' = filter_deduce_all_actions cands terms cands in

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

    deduce_fixpoint init_fixpoint init_terms

  (* memoisation *)
  let strengthen =
    let module M = struct
      type t = Symbols.table * SystemExpr.t * Sv.t * Term.messages

      let hash (tbl, s, e, terms) = 
        hcombine_list Term.hash 
          (hcombine (Symbols.tag tbl)
             (hcombine (SystemExpr.hash s)
                (Sv.hash e)))
          terms

      let equal (tbl, s, e, terms) (tbl', s', e', terms') = 
        Symbols.tag tbl = Symbols.tag tbl' &&
        s = s' && Sv.equal e e' &&
        List.length terms = List.length terms' &&
        List.for_all2 (=) terms terms' (* FIXME: term hashconsing *)

    end in
    (* FIXME: memory leaks *)
    let module Memo = Hashtbl.Make(M) in 
    let memo = Memo.create 256 in
    fun tbl s e terms ->
      try Memo.find memo (tbl, s, e, terms) with
      | Not_found -> 
        let r = strengthen tbl s e terms in
        Memo.add memo (tbl, s, e, terms) r;
        r

  (*------------------------------------------------------------------*)
  let unify ?mv table t1 t2  = `NoMgu      (* TODO *)

  let unify_opt ?mv table t1 t2 =
    match unify ?mv table t1 t2 with
    | `Freetyv | `NoMgu -> None
    | `Mgu mv -> Some mv

  (*------------------------------------------------------------------*)
  let flip = function
    | `Eq        -> `Eq
    | `Covar     -> `Contravar
    | `Contravar -> `Covar

  (*------------------------------------------------------------------*)

  (** [term_match ?vars term pat st] match [term] with [pat] w.r.t. 
      variables [vars]. *)
  let term_match_opt : type a b.
    ?vars:Sv.t ->
    a Term.term ->
    b Term.term ->
    match_state ->
    Mvar.t option
    = fun ?(vars=Sv.empty) term elem st ->
    let st = { st with support = Sv.union vars st.support; } in
    try Some (T.tmatch term elem st) 
    with NoMatch _ -> None

  (** Variant of [term_match_opt]. *)
  let term_match ?vars term pat st : Mvar.t =
    match term_match_opt ?vars term pat st with
    | None -> no_match ()
    | Some st -> st

  (*------------------------------------------------------------------*)
  (** In case [elem] is a sequence, try to match [term] as an element
      of [elem]. *)
  let seq_mem_one
      (term : Term.message)
      (elem : Term.message)
      (st   : match_state) : Mvar.t option
    =
    match elem with
    | Seq (is, elem) ->
      let is, s = Term.refresh_vars `Global is in
      let elem = Term.subst s elem in

      let is_s = Sv.of_list1 is in

      begin
        match term_match_opt ~vars:is_s term elem st with
        | None -> None
        | Some mv ->
          let mv = Mvar.filter (fun v _ -> not (Sv.mem v is_s)) mv in
          Some mv
      end

    | _ -> None

  (** Try to match [term] as an element of a sequence in [elems]. *)
  let seq_mem
      (term  : Term.message)
      (elems : Term.message list)
      (st    : match_state) : Mvar.t option
    =
    List.find_map (fun elem -> seq_mem_one term elem st) elems

  (*------------------------------------------------------------------*)
  (** Try to match [term] as an element the mset [mset]. *)
  let mset_mem_one
      (term : Term.message)
      (mset : Mset.t)
      (st   : match_state) : Mvar.t option
    =
    let tv = Vars.make_new Type.Timestamp "t" in
    let pat = Term.mk_macro mset.msymb [] (Term.mk_var tv) in

    let vars = Sv.add (Vars.EVar tv) (Sv.of_list1 mset.indices) in

    (* if [st.support] is not empty, then we need to find [mv] such that:
       - [mv] represents a substitution θ whose support is included in
         [st.support] ∪ [vars]
       - for any v ∈ [st.support], (fv(θ(v)) ∩ st.bvs = ∅)
       
       The issue is that the matching algorithm will ensure that the latter
       condition holds for ([st.support] ∪ [vars]), and not just 
       for [st.support]. This makes us reject valid instance that appear in
       practice.
       
       To allow [st.support] to be empty, we would have to modify the
       matching algorithm to account for that. 

       Instead, for now, we ensure that this issue never arise by using 
       strenghtening only is [st.support] = ∅.
    *)
    assert (Sv.is_empty st.support);
    let st = { st with bvs = Sv.empty; } in

    match term_match_opt ~vars term pat st with
    | None -> None
    | Some mv ->
      let mv = 
        Mvar.filter (fun v _ -> 
            v <> Vars.EVar tv && not (Sv.mem v vars)
          ) mv 
      in
      Some mv

  (** Try to match [term] as an element of [msets]. *)
  let mset_mem
      (term   : Term.message)
      (mset_l : Mset.t list)
      (st     : match_state) : Mvar.t option
    =
    List.find_map (fun elem -> mset_mem_one term elem st) mset_l

  (*------------------------------------------------------------------*)
  (** Duplicate checking: see [Action.is_dup_match] *)
  let is_dup
      (term  : Term.message)
      (elems : Term.message list)
      (st    : match_state) : Mvar.t option
    =
    let eterm_match (Term.ETerm t1) (Term.ETerm t2) (st : match_state) =
      match term_match_opt t1 t2 st with
      | Some mv -> Some { st with mv } 
      | None -> None
    in

    let st = Action.is_dup_match eterm_match st st.table term elems in
    omap (fun (x : match_state) -> x.mv) st
 
  (*------------------------------------------------------------------*)
  (** [fa_decompose term st] return a list of matching conditions that must be 
      met for [term] to be deducible starting from [st].
      Return [None] if Function Application fails on [term] *) 
  let fa_decompose
      (term      : Term.message)
      (st        : match_state) : (match_state * Term.message) list option
    =
    match term with
    | Term.Fun (_, _, terms) -> 
      Some (List.map (fun t -> st, t) terms)

    | Term.Atom (`Message (_, t1, t2)) ->
      Some (List.map (fun t -> st, t) [t1; t2])

    | Term.Seq (is, term) ->
      let is, subst = Term.refresh_vars `Global is in
      let term = Term.subst subst term in

      let st = { st with bvs = Sv.add_list st.bvs is; } in
      Some [(st, term)]

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
      Some [(st, term)]

    | Find (is, c, d, e) ->
      let is, subst = Term.refresh_vars `Global is in
      let c, d = Term.subst subst c, Term.subst subst d in

      let st1 = { st with bvs = Sv.add_list st.bvs is; } in

      Some [(st1, c); (st1, d); (st, e)]

    | _ -> None

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
      (st        : match_state) 
      (minfos    : match_infos) : Mvar.t * match_infos
    =
    match is_dup term pat_terms st with
    | Some mv -> mv, minfos_ok term minfos
    | None ->
      match seq_mem term pat_terms st with
    | Some mv -> mv, minfos_ok term minfos
      | None ->
        match mset_mem term mset_l st with
        | Some mv -> mv, minfos_ok term minfos
        | None ->
          (* if that fails, decompose [term] through the Function Application
             rule, and recurse. *)
          fa_match_term_incl term pat_terms mset_l st minfos 

  (** Check that [term] can be deduced from [pat_terms] through the 
      Function Application rule *) 
  and fa_match_term_incl
      (term      : Term.message)
      (pat_terms : Term.message list)
      (mset_l    : Mset.t list)
      (st        : match_state) 
      (minfos    : match_infos) : Mvar.t * match_infos
    =
    match fa_decompose term st with
    | None -> st.mv, minfos_failed term minfos

    | Some fa_conds ->
      let minfos = minfos_check_st term (List.map snd fa_conds) minfos in
      List.fold_left (fun (mv, minfos) (st, t) ->
          let mv, minfos = 
            match_term_incl t pat_terms mset_l { st with mv } minfos 
          in
          mv, minfos
        ) (st.mv, minfos) fa_conds

  (*------------------------------------------------------------------*)
  (** Greedily check entailment through an inclusion check of [terms] in
      [pat_terms]. *)
  let match_equiv_incl
      (terms     : Term.message list)
      (pat_terms : Term.message list)
      (st        : match_state) : Mvar.t
    =
    (* if [st.support] is not empty, we cannot strengthen the invariant.
       See explanation in [mset_mem_one]. *)
    let mset_l =       
      if not (Sv.is_empty st.support)
      then []
      else 
        let msets = strengthen st.table st.system st.env pat_terms in
        msets_to_list msets
    in

    if mset_l <> [] && Config.show_strengthened_hyp () then     
      (dbg ~force:true) "strengthened hypothesis:@;%a@;" pp_mset_l mset_l; 

    let mv, minfos = 
      List.fold_left (fun (mv, minfos) term ->
          match_term_incl term pat_terms mset_l { st with mv } minfos 
        ) (st.mv, Mt.empty) terms
    in

    if Mt.for_all (fun _ r -> r <> MR_failed) minfos
    then mv
    else no_match ~infos:(terms, minfos_norm minfos) ()


  (*------------------------------------------------------------------*)
  let rec match_equiv_eq
      (terms     : Term.message list)
      (pat_terms : Term.message list)
      (st        : match_state) : Mvar.t 
    =
    if List.length terms <> List.length pat_terms then no_match ();

    List.fold_right2 (fun t1 t2 mv ->
        term_match t1 t2 { st with mv }
      ) terms pat_terms st.mv

  (*------------------------------------------------------------------*)
  (** Check entailment between two equivalences.
      - [Covar]    : [pat_es] entails [es]
      - [Contravar]: [es] entails [pat_es] *)
  let tmatch_e
      ~(mode     : [`Eq | `Covar | `Contravar])
      (terms     : Term.messages)
      (pat_terms : Term.messages)
      (st        : match_state) : Mvar.t 
    =
    match mode with
    | `Eq        -> match_equiv_eq terms pat_terms st
    | `Contravar -> match_equiv_eq terms pat_terms st
    (* FIXME: in contravariant position, we cannot check for inclusion
       because, in the seq case, this requires to infer the seq
       variables for the *term* being matched. Consequently, this is no longer
       a matching problem, but is a unification problem. *)

    | `Covar     -> match_equiv_incl terms pat_terms st

  (*------------------------------------------------------------------*)
  (** Match two [Equiv.form] *)
  let rec fmatch ~mode (t : Equiv.form) (pat : Equiv.form) (st : match_state)
    : Mvar.t =
    match t, pat with
    | Impl (t1, t2), Impl (pat1, pat2) ->
      let mv = fmatch ~mode:(flip mode) t1 pat1 st in
      fmatch ~mode t2 pat2 { st with mv }

    | Atom (Reach t), Atom (Reach pat) ->
      term_match t pat st

    | Atom (Equiv es), Atom (Equiv pat_es) ->
      tmatch_e ~mode es pat_es st

    | Quant (q,es,t), Quant (q',es',t') ->
      (* TODO: match under binders  *)
      if q = q' && es = es' && t = t'
      then st.mv
      else no_match ()

    | _ -> no_match ()

  (*------------------------------------------------------------------*)
  (** Exported *)
  let try_match
      ?mv
      ?(mode=`Eq)
      (table : Symbols.table)
      (system : SystemExpr.t)
      (t : t)
      (p : t pat) : match_res
    =
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

    let mv_init = odflt Mvar.empty mv in
    let st_init : match_state =
      { bvs = Sv.empty; mv = mv_init; table; system; support; env; ty_env; }
    in
    let mode = match mode with
      | `Eq -> `Eq
      | `EntailRL -> `Covar
      | `EntailLR -> `Contravar
    in

    try
      let mv = fmatch ~mode t pat st_init in

      if not (Type.Infer.is_closed ty_env)
      then FreeTyv
      else
        let mv =
          Mvar.fold (fun (Vars.EVar v) t mv ->
              let v = Vars.tsubst ty_subst_rev v in
              Mvar.add (Vars.EVar v) t mv
            ) mv Mvar.empty
        in
        Match mv

    with NoMatch infos -> NoMatch infos


  (*------------------------------------------------------------------*)
  let map (func : f_map) (env : Vars.env) (e : Equiv.form) : Equiv.form option =
    
    let rec map
        (env : Vars.env)
        (vars : Vars.evars)
        (conds : Term.message list)
        (e : Equiv.form) : bool * Equiv.form
      =
      match e with
      | Atom (Reach f) ->
        let found, f = T._map func env ~vars ~conds f in
        let e' = Equiv.Atom (Reach f) in

        if found then true, e' else false, e

      | Atom (Equiv frame) ->
        let found, frame = List.fold_left (fun (found,acc) f ->
            let found0, f = T._map func env ~vars ~conds f in
            found0 || found, f :: acc
          ) (false,[]) frame
        in
        let frame = List.rev frame in
        let e' = Equiv.Atom (Equiv frame) in

        if found then true, e' else false, e

      | Impl (e1, e2) ->
        let found1, e1 = map env vars conds e1
        and found2, e2 = map env vars conds e2 in
        let e' = Equiv.Impl (e1, e2) in
        let found = found1 || found2 in

        if found then true, e' else false, e

      | Quant (q,vs,e0) ->
        let env, vs, s = erefresh_vars_env env vs in
        let vars = List.rev_append vs vars in
        let e0 = Equiv.subst s e0 in
        let found, b = map env vars conds e0 in
        let e' = Equiv.Quant (q,vs,b) in

        if found then true, e' else false, e
    in

    let found, e = map env [] [] e in
    match found with
    | false -> None
    | true  -> Some e
end
