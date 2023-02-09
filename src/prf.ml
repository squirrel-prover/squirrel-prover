open Utils

module Name = NameOccs.Name
                
module SE = SystemExpr
module Sv = Vars.Sv
module Sp = Match.Pos.Sp

(*------------------------------------------------------------------*)
type prf_param = {
  h_fn  : Symbols.fname; 
  h_fty : Type.ftype; 
  h_cnt : Term.term;  
  h_key : Name.t; 
}

let prf_param hash : prf_param =
  match hash with
  | Term.Fun (h_fn, h_fty, [Tuple [h_cnt; Name (key, key_args)]]) ->
    { h_fn; h_cnt; h_fty; h_key = { symb = key; args = key_args; }}

  | _ -> Tactics.soft_failure Tactics.Bad_SSC

(*------------------------------------------------------------------*)
(** Compute conjunct of PRF condition for a direct case,
  * that is an explicit occurrence of the hash in the frame. *)
let prf_mk_direct (param : prf_param) (occ : Iter.hash_occ) =
  (* select bound variables in key indices [is] and in message [m]
     to quantify universally over them *)
  let vars = occ.occ_vars in

  let vars, subst = Term.refresh_vars vars in

  let is, m = occ.occ_cnt in
  let is = List.map (Term.subst subst) is in
  let m = Term.subst subst m in
  (* let cond = Term.subst subst occ.occ_cond in *)
  let cond = Term.mk_true in
  Term.mk_forall ~simpl:true
    vars
    (Term.mk_impl
       (Term.mk_and ~simpl:true
          cond
          (Term.mk_eqs param.h_key.args is))
       (Term.mk_atom `Neq param.h_cnt m))

(*------------------------------------------------------------------*)
(** triple of the action, the key indices and the term *)
type prf_occ = (Action.action * Term.terms * Term.term) Iter.occ

(** check if all instances of [o1] are instances of [o2].
    [o1] and [o2] actions must have the same action name *)
let prf_occ_incl table sexpr (o1 : prf_occ) (o2 : prf_occ) : bool =
  let a1, is1, t1 = o1.occ_cnt in
  let a2, is2, t2 = o2.occ_cnt in

  let cond1 = Term.mk_ands (List.rev o1.occ_cond)
  and cond2 = Term.mk_ands (List.rev o2.occ_cond) in

  (* build a dummy term, which we used to match in one go all elements of
     the two occurrences *)
  let mk_dum a is cond t =
    let action = SE.action_to_term table sexpr a in
    Term.mk_ands ~simpl:false
      ((Term.mk_atom `Eq Term.init action) ::
       (Term.mk_eqs ~simpl:false is is) ::
       cond ::
       [Term.mk_atom `Eq t (Term.mk_witness (Term.ty t))])
  in
  let pat2 = Term.{
      pat_tyvars = [];
      pat_vars   = Vars.Tag.local_vars o2.occ_vars;
      (* local information, since we allow to match diff operators *)
      
      pat_term   = mk_dum a2 is2 cond2 t2;
    }
  in

  let system = SE.reachability_context sexpr in
  match Match.T.try_match table system (mk_dum a1 is1 cond1 t1) pat2 with
  | Match.FreeTyv | Match.NoMatch _ -> false
  | Match.Match _ -> true

(** Compute conjunct of PRF condition for an indirect case,
  * that is an occurence of the hash in actions of the system. *)
let prf_mk_indirect
    (cntxt         : Constr.trace_cntxt)
    (param         : prf_param)
    (frame_actions : OldFresh.deprecated_ts_occs)
    (hash_occ      : prf_occ) : Term.term
  =
  let vars = hash_occ.Iter.occ_vars in
  let vars, subst = Term.refresh_vars vars in

  let action, hash_is, hash_m = hash_occ.Iter.occ_cnt in

  (* apply [subst] to the action and to the list of
   * key indices with the hashed messages *)
  let action =
    SE.action_to_term cntxt.table cntxt.system
      (Action.subst_action subst action)
  in
  let hash_is = List.map (Term.subst subst) hash_is
  and hash_m = Term.subst subst hash_m
  and hash_cond = List.map (Term.subst subst) hash_occ.Iter.occ_cond in

  let hash_cond = Term.mk_ands (List.rev hash_cond) in

  (* condition stating that [action] occurs before a macro timestamp
     occurencing in the frame *)
  let disj = Term.mk_ors (OldFresh.deprecated_mk_le_ts_occs action frame_actions) in

  (* then if key indices are equal then hashed messages differ *)
  let form =
    Term.mk_impl
      (Term.mk_and ~simpl:true
         hash_cond
         (Term.mk_eqs param.h_key.args hash_is))
      (Term.mk_atom `Neq param.h_cnt hash_m)
  in

  Term.mk_forall ~simpl:true vars (Term.mk_impl disj form)

(*------------------------------------------------------------------*)
(** indirect case in a PRF application: PRF hash occurrence, sources *)
type prf_case = prf_occ * Term.term list

(** map from action names to PRF cases *)
type prf_cases_sorted = (Symbols.action * prf_case list) list

let add_prf_case
    table system
    (action_name : Symbols.action)
    (c : prf_case)
    (assoc_cases : prf_cases_sorted) : prf_cases_sorted
  =
  let add_case (c : prf_case) (cases : prf_case list) : prf_case list =
    let occ, srcs = c in

    (* look if [c] is subsumed by one of the element [c2] of [cases],
       in which case we update the possible sources of [c2] (note
       that this causes some loss of precision)  *)
    let found = ref false in
    let new_cases =
      List.fold_right (fun ((occ', srcs') as c2) cases ->
          if (not !found) && prf_occ_incl table system occ occ' then
            let () = found := true in
            let occ' = { occ' with occ_pos = Sp.union occ'.occ_pos occ.occ_pos } in
            (occ', srcs @ srcs') :: cases
          else c2 :: cases
        ) cases []
    in
    if !found
    then List.rev new_cases
    else c :: cases
    (* we cannot remove old cases which are subsumed by [c], because
       we also need to handle sources *)
  in

  List.assoc_up_dflt action_name [] (add_case c) assoc_cases

(*------------------------------------------------------------------*)
let mk_prf_phi_proj cntxt (env : Env.t) param frame _hash =
  (* Check syntactic side condition. *)
  let errors =
    OldEuf.key_ssc ~globals:true
      ~elems:frame ~allow_functions:(fun _ -> false)
      ~cntxt param.h_fn param.h_key.symb.s_symb
  in
  if errors <> [] then
    Tactics.soft_failure (Tactics.BadSSCDetailed errors);

  (* Direct cases: hashes from the frame. *)

  let frame_hashes : Iter.hash_occs =
    List.fold_left (fun acc t ->
        Iter.deprecated_get_f_messages_ext
          ~mode:(`Delta cntxt) (cntxt.system :> SE.arbitrary) env.table
          param.h_fn param.h_key.symb.s_symb t @ acc
      ) [] frame
  in
  let frame_hashes = List.sort_uniq Stdlib.compare frame_hashes in
  let phi_direct =
    List.map (prf_mk_direct param) frame_hashes
  in

  (* Indirect cases: potential occurrences through macro expansions. *)

  (* Compute association list from action names to prf cases. *)
  let macro_cases : prf_cases_sorted =
    Iter.fold_macro_support (fun iocc macro_cases ->
        let name = iocc.iocc_aname in
        let t = iocc.iocc_cnt in
        let fv = Sv.elements iocc.iocc_vars in

        assert (Sv.subset
                  (Term.fv iocc.iocc_cnt)
                  (Sv.union iocc.iocc_vars (Vars.to_vars_set env.vars)));
        
        let new_cases =
          Iter.deprecated_get_f_messages_ext 
            ~mode:(`Delta cntxt) (cntxt.system :> SE.arbitrary) env.table
            ~fv param.h_fn param.h_key.symb.s_symb t
        in
        let new_cases =
          List.map (fun occ ->
              let is, t = occ.Iter.occ_cnt in
              Iter.{ occ with occ_cnt = (iocc.iocc_action, is, t) }
            ) new_cases
        in

        List.fold_left (fun macro_cases new_case ->
            add_prf_case cntxt.table cntxt.system
              name (new_case, iocc.iocc_sources) macro_cases
          ) macro_cases new_cases
      ) cntxt env frame []
  in
  (* Keep only actions in which there is at least one occurrence. *)
  let macro_cases = List.filter (fun (_, occs) -> occs <> []) macro_cases in

  let phi_indirect =
    List.map (fun (_action, hash_occs) ->
        List.map (fun (hash_occ, srcs) ->
            let frame_actions = OldFresh.deprecated_get_macro_actions cntxt srcs in
            prf_mk_indirect cntxt param frame_actions hash_occ
          ) (List.rev hash_occs)
      ) (List.rev macro_cases)
  in
  let phi_indirect = List.flatten phi_indirect in

  Term.mk_ands ~simpl:true phi_direct, Term.mk_ands ~simpl:true phi_indirect

(*------------------------------------------------------------------*)
(** Build the PRF condition on one side, if the hash occurs on this side.
    Return [None] if the hash does not occurs. *)
let prf_condition_side
    (proj    : Term.proj)
    (cntxt   : Constr.trace_cntxt)
    (env     : Vars.env)
    (biframe : Equiv.equiv)
    (e       : Term.term)
    (hash    : Term.term)
  : (Term.term * Term.term) option
  =
  let exception HashNoOcc in
  try
    let system = SE.project [proj] cntxt.system in
    let cntxt = { cntxt with system } in
    let env = Env.init ~table:cntxt.table ~system:(SE.reachability_context system) ~vars:env () in
    let param = prf_param (Term.project1 proj hash) in

    (* Create the frame on which we will iterate to compute the PRF formulas *)
    let hash_ty = param.h_fty.fty_out in
    let v = Vars.make_fresh hash_ty "v" in

    let e_without_hash =
      Term.subst [Term.ESubst (hash,Term.mk_var v)] e
    in
    let e_without_hash = Term.project1 proj e_without_hash in

    (* [hash] does not appear on this side *)
    if not (Sv.mem v (Term.fv e_without_hash)) then
      raise HashNoOcc;

    let e_without_hash =
      Term.subst
        [Term.ESubst (Term.mk_var v, Term.mk_witness hash_ty)]
        e_without_hash
    in

    let frame =
      param.h_cnt :: e_without_hash :: List.map (Term.project1 proj) (biframe)
    in
    Some (mk_prf_phi_proj cntxt env param frame hash)

  with
  | HashNoOcc -> None

