open Utils

module L = Location
module Sv = Vars.Sv

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
let rev_subst subst = 
  List.map (fun (Term.ESubst (u,v)) -> Term.ESubst (v,u)) subst

(*------------------------------------------------------------------*)
type reduce_param = { delta : bool; }

let rp_full = { delta = true; }

(*------------------------------------------------------------------*)
module Mk (S : LowSequent.S) = struct
  (* TODOs: 
     - conds ignored for now.
     - trace literals not updated *)
  type state = { 
    param      : reduce_param;
    hint_db    : Hint.hint_db;
    trace_lits : Constr.trace_literals;
    conds      : Term.message list;     (* accumulated conditions *)
  }
                 
  (** Reduce a term in a given context. 
      The sequent's hypotheses must be used sparsingly *)
  let reduce_term : type a. S.t -> a Term.term -> a Term.term = fun s t ->
    let exception NoExp in
    
    (** Invariant: we must ensure that fv(reduce(u)) ⊆ fv(t)
        Return: reduced term, reduction occurred *)
    (** TODO: memoisation *)
    let rec reduce : type a. state -> a Term.term -> a Term.term * bool = 
      fun st t ->
        let t, has_red = reduce_head_once st t in

        if has_red then fst (reduce st t), true
        else
          let t, has_red = reduce_subterms st t in
          if has_red then fst (reduce st t), true
          else t, false

    (** Reduce once at head position *)
    and reduce_head_once : type a. state -> a Term.term -> a Term.term * bool = 
      fun st t ->
        let t, has_red = expand_head_once st t in
        let t, has_red' = rewrite_head_once st t in
        t, has_red || has_red'

    (** Expand once at head position *)
    and expand_head_once : type a. state -> a Term.term -> a Term.term * bool = 
      fun st t ->
        if not st.param.delta 
        then t, false 
        else try _expand_head_once st t with NoExp -> t, false

    and _expand_head_once : type a. state -> a Term.term -> a Term.term * bool = 
      fun st t ->
        match t with
        | Term.Macro (ms, l, ts) ->
          assert (l = []);
          let models = 
            match Constr.models_conjunct st.trace_lits with
            | Utils.Timeout -> raise NoExp
            | Utils.Result models -> models 
          in 
          
          if Constr.query ~precise:true models [`Pos, `Happens ts] then
            match Macros.get_definition_opt (S.mk_trace_cntxt s) ms ts with
            | None -> raise NoExp
            | Some mdef -> mdef, true
          else raise NoExp

        | _ -> raise NoExp

    (** Rewrite once at head position *)
    and rewrite_head_once : type a. state -> a Term.term -> a Term.term * bool = 
      fun st t ->
        let rule = List.find_map (fun (_, rule) ->
            match Rewrite.rewrite_head rule t with
            | None -> None
            | Some (red_t, subs) ->
              let subs_valid =  
                List.for_all (fun sub -> 
                    fst (reduce { st with param = rp_full } sub) = Term.mk_true
                  ) subs 
              in              
              if subs_valid then Some red_t else None            
          ) (Hint.get_rewrite_db st.hint_db)
        in
        
        match rule with
        | None -> t, false
        | Some red_t -> red_t, true

    (** Reduce all strict subterms *)
    and reduce_subterms : type a. state -> a Term.term -> a Term.term * bool = 
      fun st t -> 
        match t with
        | Term.Exists (evs, t0) 
        | Term.ForAll (evs, t0) -> 
          let _, subst = Term.erefresh_vars `Global evs in
          let t0 = Term.subst subst t0 in
          (* let st = { st with subst = subst @ st.subst; } in *)
          let red_t0, has_red = reduce st t0 in

          if not has_red then t, false
          else
            let r_subst = rev_subst subst in
            let red_t0 = Term.subst r_subst red_t0 in
            let red_t : Term.message = 
              match t with
              | Term.Exists _ -> Term.mk_exists ~simpl:false evs red_t0 
              | Term.ForAll _ -> Term.mk_forall ~simpl:false evs red_t0 
              | _ -> assert false
            in
            Term.cast (Term.kind t) red_t, true

        | Term.Seq (is, t0) ->
          let _, subst = Term.refresh_vars `Global is in
          let t0 = Term.subst subst t0 in
          (* let st = { st with subst = subst @ st.subst; } in *)
          let red_t0, has_red = reduce st t0 in

          if not has_red then t, false
          else
            let r_subst = rev_subst subst in
            let red_t0 = Term.subst r_subst red_t0 in
            let red_t = Term.Seq (is, red_t0) in
            Term.cast (Term.kind t) red_t, true

        | Term.Fun (fs, _, [c;t;e]) when fs = Term.f_ite -> 
          let c, has_red0 = reduce st c in

          let conds_t = c :: st.conds in
          let conds_f = (Term.mk_not ~simpl:true c) :: st.conds in

          let t, has_red1 = reduce { st with conds = conds_t } t in
          let e, has_red2 = reduce { st with conds = conds_f } e in

          Term.mk_ite ~simpl:false c t e,
          has_red0 || has_red1 || has_red2

        | Term.Find (is, c, t, e) -> 
          let _, subst = Term.refresh_vars `Global is in
          let c, t = Term.subst subst c, Term.subst subst t in
          (* let st1 = { st with subst = subst @ st.subst; } in *)
          let st1 = st in

          let c, has_red0 = reduce st1 c in

          let conds_t = c :: st.conds in
          let conds_f = (Term.mk_not ~simpl:true c) :: st.conds in

          let t, has_red1 = reduce { st1 with conds = conds_t } t in
          let e, has_red2 = reduce { st  with conds = conds_f } e in

          let r_subst = rev_subst subst in
          let c, t = Term.subst r_subst c, Term.subst r_subst t in
          
          Term.Find (is, c, t, e),
          has_red0 || has_red1 || has_red2

        | Term.Macro  _
        | Term.Name   _
        | Term.Fun    _
        | Term.Pred   _
        | Term.Action _
        | Term.Var    _
        | Term.Diff   _
        | Term.Atom   _ -> 
          let has_red, t = 
            Term.tmap_fold (fun has_red (Term.ETerm t) -> 
                let t, has_red' = reduce st t in
                has_red || has_red', Term.ETerm t
              ) false t
          in
          t, has_red

    in
    let param = { delta = false; } in
    let trace_lits = S.get_trace_literals s in
    let hint_db = S.get_hint_db s in
    let state = { param; hint_db; trace_lits; conds = []; } in
    let t, _ = reduce state t in
    t


  let rec reduce_equiv s e : Equiv.form =
    match e with
    | Equiv.Quant (q, vs, e) -> 
      let _, subst = Term.erefresh_vars `Global vs in
      let e = Equiv.subst subst e in
      let red_e = reduce_equiv s e in

      let r_subst = rev_subst subst in
      let red_e = Equiv.subst r_subst red_e in
      Equiv.Quant (q, vs, red_e)

    | Equiv.Impl (e1, e2) ->
      Equiv.Impl (reduce_equiv s e1, reduce_equiv s e2)
    
    | Equiv.Atom (Reach f) -> 
      Equiv.Atom (Reach (reduce_term s f))

    | Equiv.Atom (Equiv e) -> 
      let e = List.map (reduce_term s) e in
      Equiv.Atom (Equiv.Equiv e)

  (** We need type introspection there *)
  let reduce s (t : S.form) : S.form = match S.s_kind with
    | LowSequent.KEquiv -> reduce_equiv s t
    | LowSequent.KReach -> reduce_term  s t

end
