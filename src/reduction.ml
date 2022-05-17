open Utils

(*------------------------------------------------------------------*)
let rev_subst subst = 
  List.map (fun (Term.ESubst (u,v)) -> Term.ESubst (v,u)) subst

(*------------------------------------------------------------------*)
type red_param = { delta : bool; }

let rp_full = { delta = true; }

(*------------------------------------------------------------------*)
module type S = sig
  type t                        (* type of sequent *)

  val reduce_term  : red_param -> t -> Term.term -> Term.term     
  val reduce_equiv : red_param -> t -> Equiv.form -> Equiv.form
  val reduce       : red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a

  val destr_eq : 
    red_param -> t -> 'a Equiv.f_kind -> 'a ->
    (Term.term * Term.term) option
end

(*------------------------------------------------------------------*)
module Mk (S : LowSequent.S) : S with type t := S.t = struct
  (* FEATURE: 
     - conds ignored for now.
     - trace literals not updated *)
  type state = { 
    table      : Symbols.table;
    system     : SystemExpr.t;
    param      : red_param;
    hint_db    : Hint.hint_db;
    trace_lits : Term.literals;
    conds      : Term.term list;     (* accumulated conditions *)
  }
                 
  (** Reduce a term in a given context. 
      The sequent's hypotheses must be used sparsingly *)
  let reduce_term (param : red_param) (s : S.t) (t : Term.term) : Term.term = 
    let exception NoExp in
    
    (* Invariant: we must ensure that fv(reduce(u)) ⊆ fv(t)
       Return: reduced term, reduction occurred *)
    (* FEATURE: memoisation *)
    let rec reduce (st : state) (t : Term.term) : Term.term * bool = 
      let t, has_red = reduce_head_once st t in

      if has_red then fst (reduce st t), true
      else
        let t, has_red = reduce_subterms st t in
        if has_red then fst (reduce st t), true
        else t, false

    (* Reduce once at head position *)
    and reduce_head_once (st : state) (t : Term.term) : Term.term * bool = 
      let t, has_red  = expand_head_once st t in
      if has_red then t, true else rewrite_head_once st t 

    (* Expand once at head position *)
    and expand_head_once (st : state) (t : Term.term) : Term.term * bool = 
      if not st.param.delta 
      then t, false 
      else try _expand_head_once st t with NoExp -> t, false

    and _expand_head_once (st : state) (t : Term.term) : Term.term * bool = 
      match t with
      | Term.Macro (ms, l, ts) ->
        assert (l = []);
        let models = 
          match Constr.models_conjunct st.trace_lits with
          | Utils.Timeout -> raise NoExp
          | Utils.Result models -> models 
        in 

        if Constr.query ~precise:true models [`Pos, `Happens ts] then
          match Macros.get_definition (S.mk_trace_cntxt s) ms ts with
          | `Def mdef -> mdef, true
          | _ -> raise NoExp
        else raise NoExp

      | _ -> raise NoExp

    (* Rewrite once at head position *)
    and rewrite_head_once (st : state) (t : Term.term) : Term.term * bool = 
      let db = Hint.get_rewrite_db st.hint_db in
      let hints = Match.Hm.find_dflt [] (Match.get_head t) db in

      let rule = List.find_map (fun Hint.{ rule } ->
          match Rewrite.rewrite_head st.table st.system rule t with
          | None -> None
          | Some (red_t, subs) ->
            let subs_valid =  
              List.for_all (fun sub -> 
                  fst (reduce { st with param = rp_full } sub) = Term.mk_true
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
      | Term.Exists (evs, t0) 
      | Term.ForAll (evs, t0) -> 
        let _, subst = Term.refresh_vars `Global evs in
        let t0 = Term.subst subst t0 in
        (* let st = { st with subst = subst @ st.subst; } in *)
        let red_t0, has_red = reduce st t0 in

        if not has_red then t, false
        else
          let r_subst = rev_subst subst in
          let red_t0 = Term.subst r_subst red_t0 in
          let red_t : Term.term = 
            match t with
            | Term.Exists _ -> Term.mk_exists ~simpl:false evs red_t0 
            | Term.ForAll _ -> Term.mk_forall ~simpl:false evs red_t0 
            | _ -> assert false
          in
          red_t, true

      | Term.Seq (is, t0) ->
        let _, subst = Term.refresh_vars `Global is in
        let t0 = Term.subst subst t0 in
        (* let st = { st with subst = subst @ st.subst; } in *)
        let red_t0, has_red = reduce st t0 in

        if not has_red then t, false
        else
          let r_subst = rev_subst subst in
          let red_t0 = Term.subst r_subst red_t0 in
          let red_t = Term.mk_seq0 is red_t0 in
          red_t, true

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

        Term.mk_find is c t e,
        has_red0 || has_red1 || has_red2

      | Term.Macro  _
      | Term.Name   _
      | Term.Fun    _
      | Term.Action _
      | Term.Var    _
      | Term.Diff   _ -> 
        let has_red, t = 
          Term.tmap_fold (fun has_red t -> 
              let t, has_red' = reduce st t in
              has_red || has_red', t
            ) false t
        in
        t, has_red

    in
    let state = { 
      table      = S.table s;
      system     = (S.system s).set; (* TODO quickfix might be abusive *)
      param      = param;
      hint_db    = S.get_hint_db s;
      trace_lits = S.get_trace_literals s;
      conds      = []; 
    } in
    let t, _ = reduce state t in
    t


  let rec reduce_equiv (param : red_param) s e : Equiv.form =
    match e with
    | Equiv.Quant (q, vs, e) -> 
      let _, subst = Term.refresh_vars `Global vs in
      let e = Equiv.subst subst e in
      let red_e = reduce_equiv param s e in

      let r_subst = rev_subst subst in
      let red_e = Equiv.subst r_subst red_e in
      Equiv.Quant (q, vs, red_e)

    | Equiv.And (e1, e2) ->
      Equiv.And (reduce_equiv param s e1, reduce_equiv param s e2)

    | Equiv.Or (e1, e2) ->
      Equiv.Or (reduce_equiv param s e1, reduce_equiv param s e2)

    | Equiv.Impl (e1, e2) ->
      Equiv.Impl (reduce_equiv param s e1, reduce_equiv param s e2)
    
    | Equiv.Atom (Reach f) -> 
      Equiv.Atom (Reach (reduce_term param s f))

    | Equiv.Atom (Equiv e) -> 
      let e = List.map (reduce_term param s) e in
      Equiv.Atom (Equiv.Equiv e)

  (** We need type introspection there *)
  let reduce (type a) 
      (param : red_param) (s : S.t) (k : a Equiv.f_kind) (x : a) : a 
    =
    match k with
    | Local_t  -> reduce_term  param s x
    | Global_t -> reduce_equiv param s x
    | Any_t ->
       match x with
         | `Reach x -> `Reach (reduce_term param  s x)
         | `Equiv x -> `Equiv (reduce_equiv param s x)

 (*------------------------------------------------------------------*)
  (* FIXME: use [param] and [s] to reduce [x] if necessary *)
  let destr_eq (type a)
      (param : red_param) (s : S.t) (k : a Equiv.f_kind)
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
      | `Reach x ->   destr_eq x
      | `Equiv x -> e_destr_eq x
end

