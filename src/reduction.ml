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
  constr : bool;
}

let rp_default = { delta = false; constr = false; }

let rp_full = { delta = true; constr = false; }

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
module type S = sig
  type t                        (* type of sequent *)

  val reduce_term : 
    ?expand_context:Macros.expand_context ->
    ?se:SE.t -> red_param -> t -> Term.term -> Term.term     

  val reduce_equiv : 
    ?expand_context:Macros.expand_context ->
    ?system:SE.context -> red_param -> t -> Equiv.form -> Equiv.form

  val reduce : 
    ?expand_context:Macros.expand_context ->
    ?system:SE.context -> red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a

  val expand_head_once :
    ?expand_context:Macros.expand_context ->
    ?se:SE.t -> 
    red_param -> t -> Term.term -> Term.term * bool

  val destr_eq : 
    t -> 'a Equiv.f_kind -> 'a -> (Term.term * Term.term) option
end

(*------------------------------------------------------------------*)
module Mk (S : LowSequent.S) : S with type t := S.t = struct
  type state = { 
    table   : Symbols.table;
    sexpr   : SE.arbitrary;
    param   : red_param;
    hint_db : Hint.hint_db;
    hyps    : THyps.hyps;

    expand_context : Macros.expand_context;
    (** expantion mode for macros. See [Macros.expand_context]. *)
  }

  (** Internal *)
  exception NoExp 

  let add_hyp (f : Term.term) hyps : THyps.hyps =
    THyps.add TacticsArgs.AnyName (`Reach f) hyps

  
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
    if has_red then t, true else
      let t, has_red = rewrite_head_once st t in
      if has_red then t, true else
      if Term.ty t <> Type.Boolean then t, false
      else reduce_constr st t

  (* Try to show using [Constr] that [t] is [false] or [true] *)
  and reduce_constr (st : state) (t : Term.term) : Term.term * bool =
    if not st.param.constr then t, false
    else
      try
        if not Constr.(m_is_sat (models_conjunct ~exn:NoExp [t]))
        then Term.mk_false, true
        else if not Constr.(m_is_sat (models_conjunct ~exn:NoExp [Term.mk_not t]))
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
    let db = Hint.get_rewrite_db st.hint_db in
    let hints = Term.Hm.find_dflt [] (Term.get_head t) db in

    let rule = List.find_map (fun Hint.{ rule } ->
        match 
          Rewrite.rewrite_head
            st.table st.expand_context (lazy st.hyps) st.sexpr 
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
    | Term.Exists (evs, t0) 
    | Term.ForAll (evs, t0) -> 
      let _, subst = Term.refresh_vars `Global evs in
      let t0 = Term.subst subst t0 in
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
      let red_t0, has_red = reduce st t0 in

      if not has_red then t, false
      else
        let r_subst = rev_subst subst in
        let red_t0 = Term.subst r_subst red_t0 in
        let red_t = Term.mk_seq0 is red_t0 in
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
      let _, subst = Term.refresh_vars `Global is in
      let c, t = Term.subst subst c, Term.subst subst t in
      let st1 = st in

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
  let mk_state ~expand_context ~se (param : red_param) (s : S.t) : state = 
    { table   = S.table s;
      sexpr   = se;
      param;
      hint_db = S.hint_db s;
      hyps    = S.get_trace_hyps s; 
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
    let state = mk_state ~expand_context ~se param s in
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
    let state = mk_state ~expand_context ~se param s in
    let t, _ = reduce state t in
    t

  (** Exported. *)
  let rec reduce_equiv
      ?(expand_context : Macros.expand_context = InSequent)
      ?(system : SE.context option)
      (param : red_param) (s : S.t) (e : Equiv.form) : Equiv.form 
    =
    let reduce_equiv = reduce_equiv ~expand_context in
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
      let system = odflt (S.system s) system in
      let e_se = (oget system.pair :> SE.arbitrary) in
      let state = mk_state ~expand_context ~se:e_se param s in

      let e = List.map (fst -| reduce state) e in
      Equiv.Atom (Equiv.Equiv e)

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
      | `Reach x -> `Reach (reduce_term  ~expand_context ?se     param s x)
      | `Equiv x -> `Equiv (reduce_equiv ~expand_context ?system param s x)

 (*------------------------------------------------------------------*)
  (* FIXME: use [s] to reduce [x] if necessary *)
  let destr_eq (type a)
      (s : S.t) (k : a Equiv.f_kind)
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

