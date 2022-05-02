open Utils

module SE = SystemExpr
module Sv = Vars.Sv
module Sp = Match.Pos.Sp

(*------------------------------------------------------------------*)
type prf_param = {
  h_fn  : Term.fname;  (** function name *)
  h_fty : Type.ftype;  (** Hash function type *)
  h_cnt : Term.term;   (** contents, i.e. hashed message *)
  h_key : Term.nsymb;  (** key *)
}

let prf_param hash : prf_param =
  match hash with
  | Term.Fun ((h_fn, _), h_fty, [h_cnt; Name h_key]) ->
    { h_fn; h_cnt; h_fty; h_key }

  | _ -> Tactics.soft_failure Tactics.Bad_SSC

(*------------------------------------------------------------------*)
(** Compute conjunct of PRF condition for a direct case,
  * that is an explicit occurrence of the hash in the frame. *)
let prf_mk_direct env (param : prf_param) (occ : Iter.hash_occ) =
  (* select bound variables in key indices [is] and in message [m]
     to quantify universally over them *)
  let env = ref env in

  let vars = occ.occ_vars in

  let vars, subst = Term.refresh_vars (`InEnv env) vars in

  let is, m = occ.occ_cnt in
  let is = List.map (Term.subst_var subst) is in
  let m = Term.subst subst m in
  (* let cond = Term.subst subst occ.occ_cond in *)
  let cond = Term.mk_true in
  Term.mk_forall ~simpl:true
    vars
    (Term.mk_impl
       (Term.mk_and ~simpl:true
          cond
          (Term.mk_indices_eq param.h_key.s_indices is))
       (Term.mk_atom `Neq param.h_cnt m))

(*------------------------------------------------------------------*)
(** triple of the action, the key indices and the term *)
type prf_occ = (Action.action * Vars.var list * Term.term) Iter.occ

(** check if all instances of [o1] are instances of [o2].
    [o1] and [o2] actions must have the same action name *)
let prf_occ_incl table system (o1 : prf_occ) (o2 : prf_occ) : bool =
  let a1, is1, t1 = o1.occ_cnt in
  let a2, is2, t2 = o2.occ_cnt in

  let cond1 = Term.mk_ands (List.rev o1.occ_cond)
  and cond2 = Term.mk_ands (List.rev o2.occ_cond) in

  (* build a dummy term, which we used to match in one go all elements of
     the two occurrences *)
  let mk_dum a is cond t =
    let action = SE.action_to_term table system a in
    Term.mk_ands ~simpl:false
      ((Term.mk_atom `Eq Term.init action) ::
       (Term.mk_indices_eq ~simpl:false is is) ::
       cond ::
       [Term.mk_atom `Eq t (Term.mk_witness (Term.ty t))])
  in
  let pat2 = Match.{
      pat_tyvars = [];
      pat_vars   = Sv.of_list o2.occ_vars;
      pat_term   = mk_dum a2 is2 cond2 t2;
    }
  in

  match Match.T.try_match table (system:>SE.t) (mk_dum a1 is1 cond1 t1) pat2 with
  | Match.FreeTyv | Match.NoMatch _ -> false
  | Match.Match _ -> true

(** Compute conjunct of PRF condition for an indirect case,
  * that is an occurence of the hash in actions of the system. *)
let prf_mk_indirect
    (env           : Vars.env)
    (cntxt         : Constr.trace_cntxt)
    (param         : prf_param)
    (frame_actions : Fresh.ts_occs)
    (hash_occ      : prf_occ) : Term.term
  =
  let env = ref env in
  
  let vars = hash_occ.Iter.occ_vars in
  let vars, subst = Term.refresh_vars (`InEnv env) vars in

  let action, hash_is, hash_m = hash_occ.Iter.occ_cnt in

  (* apply [subst] to the action and to the list of
   * key indices with the hashed messages *)
  let action =
    SE.action_to_term cntxt.table cntxt.system
      (Action.subst_action subst action)
  in
  let hash_is = List.map (Term.subst_var subst) hash_is
  and hash_m = Term.subst subst hash_m
  and hash_cond = List.map (Term.subst subst) hash_occ.Iter.occ_cond in

  let hash_cond = Term.mk_ands (List.rev hash_cond) in

  (* save the environment after having renamed all free variables until now. *)
  let env0 = !env in
  (* condition stating that [action] occurs before a macro timestamp
     occurencing in the frame *)
  let disj = Term.mk_ors (Fresh.mk_le_ts_occs env0 action frame_actions) in

  (* then if key indices are equal then hashed messages differ *)
  let form =
    Term.mk_impl
      (Term.mk_and ~simpl:true
         hash_cond
         (Term.mk_indices_eq param.h_key.s_indices hash_is))
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
let mk_prf_phi_proj cntxt env param frame hash =
  (* Check syntactic side condition. *)
  let errors =
    Euf.key_ssc ~globals:false
      ~elems:frame ~allow_functions:(fun x -> false)
      ~cntxt param.h_fn param.h_key.s_symb
  in
  if errors <> [] then
    Tactics.soft_failure (Tactics.BadSSCDetailed errors);

  (* Direct cases: hashes from the frame. *)

  let frame_hashes : Iter.hash_occs =
    List.fold_left (fun acc t ->
        Iter.get_f_messages_ext ~mode:(`Delta cntxt) 
          param.h_fn param.h_key.s_symb t @ acc
      ) [] frame
  in
  let frame_hashes = List.sort_uniq Stdlib.compare frame_hashes in
  let phi_direct =
    List.map (prf_mk_direct env param) frame_hashes
  in

  (* Indirect cases: potential occurrences through macro expansions. *)

  (* Compute association list from action names to prf cases. *)
  let macro_cases : prf_cases_sorted =
    Iter.fold_macro_support (fun iocc macro_cases ->
        let name = iocc.iocc_aname in
        let t = iocc.iocc_cnt in
        let fv = (Sv.elements iocc.iocc_vars) in

        let new_cases =
          Iter.get_f_messages_ext ~mode:(`Delta cntxt)
            ~fv param.h_fn param.h_key.s_symb t
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
    List.map (fun (action, hash_occs) ->
        List.map (fun (hash_occ, srcs) ->
            let frame_actions = Fresh.get_macro_actions cntxt srcs in
            prf_mk_indirect env cntxt param frame_actions hash_occ
          ) (List.rev hash_occs)
      ) (List.rev macro_cases)
  in
  let phi_indirect = List.flatten phi_indirect in

  Term.mk_ands ~simpl:true phi_direct, Term.mk_ands ~simpl:true phi_indirect


(** Build the PRF condition on one side, if the hash occurs on this side.
    Return [None] if the hash does not occurs. *)
let prf_condition_side
    (proj : Term.projection)
    (cntxt : Constr.trace_cntxt)
    (env : Vars.env)
    (biframe : Equiv.equiv)
    (e : Term.term)
    (hash : Term.term) : (Term.form * Term.form) option
  =
  let exception HashNoOcc in
  try
    let system = SE.(singleton (project proj cntxt.system)) in
    let cntxt = { cntxt with system } in
    let param = prf_param (Term.project1 proj hash) in

    (* Create the frame on which we will iterate to compute the PRF formulas *)
    let hash_ty = param.h_fty.fty_out in
    let v = Vars.make_new hash_ty "v" in

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

(* From two conjunction formulas p and q, produce a minimal diff(p, q),
 * of the form (p inter q) && diff (p minus q, q minus p). *)
let combine_conj_formulas p q =
  (* Turn the conjunctions into lists. *)
  let p, q = Term.decompose_ands p, Term.decompose_ands q in
  let aux_q = ref q in
  let (common, new_p) = List.fold_left (fun (common, r_p) p ->
      (* If an element of p is inside aux_q, remove it from aux_q and
       * add it to common, else add it to r_p. *)
      if List.mem p !aux_q then
        (aux_q := List.filter (fun e -> e <> p) !aux_q; (p::common, r_p))
      else
        (common, p::r_p))
      ([], []) p
  in
  (* [common] is the intersection of p and q,
   * [aux_q] is the remainder of q and
   * [new_p] the remainder of p. *)
  Term.mk_and
    (Term.mk_ands common)
    (Term.head_normal_biterm
       (Term.mk_diff [Term.left_proj,  Term.mk_ands new_p;
                      Term.right_proj, Term.mk_ands (List.rev !aux_q)]))
