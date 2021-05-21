open Utils

(* module L = Location
 * module TS = TraceSequent *)

module Sv = Vars.Sv

(*------------------------------------------------------------------*)
let rev_subst subst = 
  List.map (fun (Term.ESubst (u,v)) -> Term.ESubst (u,v)) subst

(*------------------------------------------------------------------*)

let rules : Rewrite.rw_erule list = []

(*------------------------------------------------------------------*)
module Mk (S : LowSequent.S) = struct

  (* TODOs: 
     - conds ignored for now.
     - macros not expanded for now. *)
  type state = { 
    trace_lits : Constr.trace_literals;
    subst      : Term.esubst list; (* propagated downward, not yet applied *)
    conds      : Term.message list;     (* accumulated conditions *)
  }
                 
  (** Reduce a term in a given context. 
      The sequent's hypotheses must be used sparsingly *)
  let reduce : type a. S.t -> a Term.term -> a Term.term = fun s t ->
    
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

    (* (** Return: reduces terms, at least one term reduced  *)
     * and reduces : type a. state -> a Term.term list -> a Term.term list * bool = 
     *   fun st ts ->
     *     ts, false *)

    (** Reduce once at head position *)
    and reduce_head_once : type a. state -> a Term.term -> a Term.term * bool = 
      fun st t ->
        let rule = List.find_map (fun rule ->
            match Rewrite.rewrite_head rule t with
            | None -> None
            | Some (red_t, subs) ->
              let subs_valid =  
                List.for_all (fun sub -> 
                    fst (reduce st sub) = Term.mk_true
                  ) subs 
              in              
              if subs_valid then Some red_t else None            
          ) rules 
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
          let st = { st with subst = subst @ st.subst; } in
          let red_t0, has_red = reduce st t0 in

          if not has_red then t, false
          else
            let r_subst =
              List.map (fun (Term.ESubst (u,v)) -> Term.ESubst (u,v)) subst
            in
            let red_t0 = Term.subst r_subst red_t0 in
            let red_t : Term.message = 
              match t with
              | Term.Exists _ -> Term.mk_exists ~simpl:true evs red_t0 
              | Term.ForAll _ -> Term.mk_forall ~simpl:true evs red_t0 
              | _ -> assert false
            in
            Term.cast (Term.kind t) red_t, true

        | Term.Seq (is, t0) ->
          let _, subst = Term.refresh_vars `Global is in
          let st = { st with subst = subst @ st.subst; } in
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
          let st1 = { st with subst = subst @ st.subst; } in

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
    let state = { trace_lits = []; subst = []; conds = []; } in
    let t, _ = reduce state t in
    t

end
