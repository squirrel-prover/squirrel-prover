(* IND-CCA1 equiv tactic *)
open Squirrelcore
open Term
open Utils

module Args = TacticsArgs
module L = Location
module SE = SystemExpr
module NO = NameOccs
module ER = EncRandom
module ES = EquivSequent
module LT = LowTactics
module T = ProverTactics

module Name = Occurrences.Name

type sequent = ES.sequent


module MP = Match.Pos
module Sp = MP.Sp


(*------------------------------------------------------------------*)
let wrap_fail = LT.EquivLT.wrap_fail
let soft_failure = Tactics.soft_failure


(** Replaces any name with the same symbol as n with tsub in t.
    Use at your own risks when n has arguments
    (will not recursively look in them) *)
let rec subst_name (n:Name.t) (tsub:Term.term) (t:Term.term) : term =
  match t with
  | Name (n', _) when n' = n.symb -> tsub
  | _ -> Term.tmap (subst_name n tsub) t


(** Checks that there is no diff or binder in t above any name
    with the same symbol as n.
    Does not unfold any macro (meant to be used after rewriting
    in indcca_param, so we know that no occurrence of n can be
    under a macro) *)
let rec check_nodiffbind (n:Name.t) (t:term) : bool =
  if not (ER.has_name n t) then true
  else
    match t with
    | Diff (Explicit _) -> false
    | _ when Term.is_binder t -> false
    | _ -> Term.tforall (check_nodiffbind n) t


(** Returns true iff f is a symmetric or asymmetric encryption function. *)
let is_enc (table:Symbols.table) (f:Symbols.fname) =
  Symbols.(is_ftype f AEnc table || is_ftype f SEnc table)

(** Returns true iff t contains an encryption function.
    Does not unfold macros. *)
let rec has_enc (table:Symbols.table) (t:term) : bool =
  match t with
  | Term.Fun (f, _) when is_enc table f -> true
  | _ -> Term.texists (has_enc table) t

(** Checks that each term ti in ts is f(argsi) for the same f,
    if so returns f and the list [args1;…;argsn].
    Does the same if each ti is Tuple(argsi). *)
let same_head_function (ts:Term.terms) :
  ((Symbols.fname * applied_ftype) option * Term.terms list) option =
  let rec aux ts f =
    match ts, f with
    | [], _ -> f
    | (Term.App (Fun (fs', ft'), args))::ll, Some (Some (fs, ft), largs)
      when fs = fs' && ft = ft' ->
      aux ll (Some (Some (fs, ft), args::largs))
    | (Term.App (Fun (fs, ft), args))::ll, None ->
      aux ll (Some (Some (fs, ft), [args]))
    | (Term.Tuple args)::ll, Some (None, largs) ->
      aux ll (Some (None, args::largs))
    | (Term.Tuple args)::ll, None ->
      aux ll (Some (None, [args]))
    | _ -> None
  in
  aux (List.rev ts) None

(** Moves any diff that is above an encryption function down
    as much as possible, stopping once it gets under the enc.
    Also moves diffs under tuples. *)
(* TODO this is very ad hoc, do we have a generic mechanism for this?
   If not, do we want one? *)
let rec move_diff (table:Symbols.table) (t:term) : term =
  match t with
  | Diff (Explicit l) ->
    let (lp, lt) = List.split l in
    begin
      match same_head_function lt with
      | Some (Some (fs, ft), largs) when has_enc table t ->
        (* diff over a function -> move it under
           (only if there is still an enc below) *)
        let largs = List.megacombine largs in
        let largs = List.map
            (fun args -> Term.mk_diff (List.combine lp args))
            largs
        in
        let t = Term.mk_fun0 fs ft largs in
        Term.tmap (move_diff table) t

      | Some (None, largs) ->
        (* diff over a tuple -> move it under *)
        let largs = List.megacombine largs in
        let largs = List.map
            (fun args -> Term.mk_diff (List.combine lp args))
            largs
        in
        let t = Term.mk_tuple largs in
        Term.tmap (move_diff table) t

      | _ -> Term.tmap (move_diff table) t
    end
  | _ -> Term.tmap (move_diff table) t
      
  

(*------------------------------------------------------------------*)
(** IND-CCA tactic *)

(** parameters for the indcca tactic *)
type indcca_param = {
  ip_enc     : Symbols.fname;        (* encryption function *)
  ip_dec     : Symbols.fname;        (* decryption function *)
  ip_pk      : Symbols.fname option; (* associated public key function,
                                        for the asymmetric case *)
  ip_context : Term.term;            (* context around the ciphertext *)
  ip_cname   : Name.t;               (* fresh name standing in for the
                                        ciphertext in the context *)
  ip_table   : Symbols.table;        (* updated table with an entry xc *)
  ip_plain   : Term.term;            (* plaintext *)
  ip_rand    : Term.term;            (* randomness *)
  ip_key     : Term.term;            (* key. Note: we don't force the rand
                                        and key to be names, as they may be
                                        eg diffs. We check later (after
                                        projection) that we get names. *)
}

(*------------------------------------------------------------------*)
(** Finds the parameters of the cca application *)
let indcca_param
    ~(loc:L.t)
    (t:Term.term)    (* element in the goal where we want to apply cca *)
    (s:sequent)    
  : indcca_param
  = 
  let table = ES.table s in
  let secontx = ES.system s in
  let sys = ES.get_system_pair s in 
  let hyps = ES.get_trace_hyps s in
  let t = move_diff table t in (* move the diffs under the enc,
                                            as much as possible *)

  (* rw_rule trying to rewrite an instance of f(xm,xr,xk) into xc *)
  (* use "Tuple [xm;xr;xk]" to retrieve the value of vars once instantiated *) 
  let mk_rewrule
      (f:Symbols.fname)
      (cty:Type.ty) (mty:Type.ty) (rty:Type.ty) (kty:Type.ty) :
    Rewrite.rw_rule * Symbols.table * Name.t =
    let n_fty = Type.mk_ftype [] [] cty in
    let xcdef = Symbols.{n_fty} in
    let s = (L.mk_loc L._dummy "X") in
    let table, xcs =
      Symbols.Name.declare table s xcdef
    in

    let xc = Name.{symb=Term.mk_symb xcs cty; args=[]} in
    let xm = Vars.make_fresh mty "M" in
    let xr = Vars.make_fresh rty "R" in
    let xk = Vars.make_fresh kty "K" in
    {rw_tyvars = [];
     rw_system = SE.to_arbitrary sys;
     rw_vars   = Vars.Tag.local_vars [xm; xr; xk];
     (* local information, since we allow to match diff operators *)
     
     rw_conds  = [mk_eq ~simpl:false
                   (mk_tuple [mk_var xm; mk_var xr; mk_var xk])
                   (Prelude.mk_witness table ~ty_arg:(Type.tuple [mty; rty; kty]))];
     rw_rw     = (mk_fun_tuple table f [mk_var xm; mk_var xr; mk_var xk]),
                 (Name.to_term xc);
     rw_kind   = GlobalEq;
    },
    table,
    xc
  in
  
  (* go through all encryption functions, try to find a ciphertext *)
  let res = Symbols.Function.fold
      (fun f _ _ x -> (* for all functions:*)
         match x with
         | None when is_enc table f ->
           (* f is an encryption symbol: try to find a ctxt *)
           let fty, _ = Symbols.Function.get_def f table in
           let cty = fty.fty_out in
           let mty, rty, kty =
             match fty.fty_args with
             | [Type.Tuple [x;y;z]] -> x,y,z
             | _ -> assert false
           in
           
           let rule, table, xc = mk_rewrule f cty mty rty kty in
           let res =
             Rewrite.rewrite
               table
               Vars.empty_env
               (* only local variables, hence [env] is useless here *)

               secontx InSequent hyps TacticsArgs.Once
               rule
               Equiv.(Global (Atom (Equiv [t])))
           in
           begin
             match res with
             | Rewrite.RW_Result rr -> Some (f, rr, table, xc)
             | _ -> None
           end           
         | _ -> x) (* already found, or f is another function *)
      None
      table
  in

  match res with
  | None -> (* no ciphertext was rewritten *)
    soft_failure ~loc (Tactics.Failure "no ciphertext found")
      
  | Some (enc_f, (ccc, [(_, l)]), table, xc) -> (* a ciphertext was found *)
    let dec_f, pk_f = (* get the associated dec and pk functions *)
      match Symbols.Function.get_data enc_f table with
      | Symbols.AssociatedFunctions [dec_f] -> (* sym enc *)
        (* sanity checks *)
        assert (Symbols.is_ftype enc_f Symbols.SEnc table);
        assert (Symbols.is_ftype dec_f Symbols.SDec table);
        dec_f, None
      | Symbols.AssociatedFunctions [dec_f; pk_f] -> (* asym enc *)
        (* sanity checks *)
        assert (Symbols.is_ftype enc_f Symbols.AEnc table);
        assert (Symbols.is_ftype dec_f Symbols.ADec table);
        assert (Symbols.is_ftype pk_f Symbols.PublicKey table);
        dec_f, (Some pk_f)
      | _ -> assert false
    in

    (* get the context *)
    let cc =
      match (Equiv.any_to_equiv ccc) with
      | Equiv.(Atom (Equiv [cc])) -> cc
      | _ -> assert false
    in
                  
    (* get the content of variables from the conditions *)
    (* extract the last thing in l, in case additional conditions
       were collected *)
    (* also remove universally quantified variables that may have been
       introduced in the condition. Note that in that case, m,r,k will
       contain free variables. This is not an issue: since there must 
       be a quantifier above the ciphertext we found, the tactic will
       fail anyway later on *)
    let l = snd (decompose_impls_last (snd (decompose_forall l))) in
    let m,r,k =
      match l with
      | Term.(App (Fun (ff, _), [Tuple [m; r; k]; _])) when
          ff = Term.f_eq ->
        m,r,k
      | _ -> assert false
    in

    (* only thing left is checking there's no diff or binders
       above xc in cc *)
    if not (check_nodiffbind xc cc) then 
      soft_failure ~loc
        (Tactics.Failure 
           "no diff or binder allowed above the ciphertext for cca");
    (* return the parameters *)
    {ip_enc=enc_f; ip_dec=dec_f; ip_pk=pk_f; ip_context=cc;
     ip_cname=xc; ip_plain=m; ip_rand=r; ip_key=k; ip_table=table}

  | _ -> assert false
        
        
(*------------------------------------------------------------------*)
(** Constructs the formula expressing that in the proj
    of (the biframe + the context cc
       the plaintext m, the random r, the key k):
   - no decryption with k is present above var xc in cc
   - the proj of k is correctly used
   - the proj of the randomness r does not occur elsewhere
   - the other randoms are fresh.
   Note that cc contains a name xc meant to be replaced with the ciphertext.
   So we take subcs: a list of terms to substitute xc with in
   the resulting formula (we generate a copy of the formula for each element
   of subcs).
   IMPORTANT: this only works because we don't apply CCA under binders, so
   subc contains no free vars and can just be substituted anywhere. *)
let phi_proj
    ?use_path_cond
    (loc     : L.t)
    (env     : Env.t)
    (contx   : Constr.trace_cntxt)
    (enc_f   : Symbols.fname)
    (dec_f   : Symbols.fname)
    (pk_f    : Symbols.fname option)
    (biframe : terms)
    (cc      : term)   (* context above the ciphertext in the goal *)
    (m       : term)
    (k       : term)
    (r       : term)
    (xc      : Name.t) (* stand-in for the ciphertext in cc. *)
    (subcs   : terms) (* what to substitute xc with in the end *)
    (proj    : proj)
  : Term.terms
  =
  (* project everything *)
  let system_p = SE.project [proj] contx.system in
  let env = Env.update ~system:{ env.system with set = (system_p :> SE.arbitrary); } env in
  let contx_p = { contx with system = system_p } in
  let cc_p = Term.project1 proj cc in
  let m_p = Term.project1 proj m in
  let subcs_p = List.map (Term.project1 proj) subcs in

  (* check that the rand and key, once projected, are names. *)
  let k_p, r_p = 
    match pk_f, Term.project1 proj k, Term.project1 proj r with
    | None, (Name _ as kp), (Name _ as rp) -> (* sym enc: key is a name *)
      Name.of_term kp, Name.of_term rp
    | (Some pk_f), (Term.(App (Fun (pk_f',_),[Name _ as kp]))), (Name _ as rp)
        when pk_f = pk_f' -> (* asym enc: key is a pk *)
      Name.of_term kp, Name.of_term rp        
    | _ -> soft_failure ~loc
             (Tactics.Failure "Can only be applied on an encryption \
                               where the random and (secret) key are names.")
  in
  let frame_p = List.map (Term.project1 proj) biframe in

  let pp_kr ppf () = Fmt.pf ppf "%a and %a" Name.pp k_p Name.pp r_p in
  let pp_rand ppf () = Fmt.pf ppf "randomness" in

  let dummy_cipher =              (* dummy ciphertext, needed by [EncRandom] *)
    Prelude.mk_witness env.table ~ty_arg:(Symbols.ftype env.table enc_f).Type.fty_out
  in
  (* get the bad key and randomness occs, and the ciphertexts,
     in frame + m + kargs + rargs. There, decryption with k is allowed. *) 
  let get_bad_krc = 
    ER.get_bad_occs_and_ciphertexts env
      k_p [r_p] dummy_cipher enc_f dec_f ~hash_f:None ~pk_f
  in
  (* discard the formulas generated for the ciphertexts themselves,
     we don't use them for cca *)
  let phis_kr, _, _, ciphertexts =
    NO.occurrence_formulas_with_occs ~mode:PTimeSI ~negate:true ~pp_ns:(Some pp_kr)
      ER.ciphertext_formula
      (get_bad_krc ~dec_allowed:ER.Allowed) contx_p env
      (m_p :: k_p.args @ r_p.args @ frame_p)
  in

  (* also get bad key and rand occs, and ciphertexts in the context cc.
     There, decryption with k is allowed ONLY on subterms that do not contain
     the variable xc (which stands for the challenge) *)
  let phis_kr_cc, _, _, ciphertexts_cc =
    NO.occurrence_formulas_with_occs ~mode:PTimeSI ~negate:true ~pp_ns:(Some pp_kr)
      ER.ciphertext_formula
      (get_bad_krc ~dec_allowed:(ER.NotAbove xc)) contx_p env [cc_p]
  in

  let phis_kr = phis_kr @ phis_kr_cc in
  let ciphertexts = ciphertexts @ ciphertexts_cc in
  
  (* in addition, the edge case where k and r have the same symbol generates an
     additional condition: they must have different arguments.
     since the ciphertext can't contain binders, the formula is easy.
     If it could, it would need to be updated. *)
  let phis_kr =
    if k_p.symb.s_symb = r_p.symb.s_symb then
      (mk_neqs ~simpl:true ~simpl_tuples:true k_p.args r_p.args) :: phis_kr
    else
      phis_kr
  in

  (* formulas for the random freshness ONLY for symmetric enc *)
  let get_bad_randoms =
    ER.get_bad_randoms env k_p ciphertexts enc_f
  in
  let _, phis_random =
    if pk_f <> None then
      NO.occurrence_formulas ~mode:PTimeSI ?use_path_cond ~negate:true ~pp_ns:(Some pp_rand)
        (ER.randomness_formula ?use_path_cond)
        get_bad_randoms contx_p env (cc_p :: m_p :: k_p.args @ r_p.args @ frame_p)
    else
      [], []
  in

  (* finally, apply the substitution to the variable in cc *)
  (* IT ONLY WORKS if all vars in the ciphertext are bound in the env,
     not in binders *)
  let phi_p =
    List.concat_map
      (fun c -> List.map (subst_name xc c) (phis_kr @ phis_random))
      subcs_p
  in 
  
  (* not removing duplicates here, we'll need to remove duplicates
     between phi_l and phi_r later anyway *)
  phi_p


(*------------------------------------------------------------------*)
(** The IND-CCA1 tactic  *)
let indcca1 (i:int L.located) (s:sequent) : sequent list =
  let contx = ES.mk_pair_trace_cntxt s in
  let table = contx.table in
  let env = ES.env s in
  let loc = L.loc i in

  let proj_l, proj_r = ES.get_system_pair_projs s in

  let before, e, after = LT.split_equiv_conclusion i s in
  let biframe = List.rev_append before after in
  
  
  (* get the parameters, enforcing that
     cc does not contain diffs or binders above xc.
     (at least the diff part could maybe be relaxed?) *)
  let {ip_enc=enc_f; ip_dec=dec_f; ip_pk=pk_f; ip_context=cc;
       ip_cname=xc; ip_table=tablexc; ip_plain=m; ip_rand=r; ip_key=k} =
    indcca_param ~loc e s
  in
  let contxxc = {contx with table=tablexc} in

  (* the ciphertext, and the ciphertext encrypting its length instead of m *)
  let c = Term.(mk_fun table enc_f [mk_tuple [m; r; k]]) in
  let c_len = 
    Term.(mk_fun table enc_f [mk_tuple [Prelude.mk_zeroes table (mk_len m); r; k]]) 
  in

  let phi_proj =
    phi_proj ~use_path_cond:false loc env contxxc enc_f dec_f pk_f biframe cc m k r xc [c; c_len]
    (* FEATURE: allow the user to set [use_path_cond] to true *)
  in


  Printer.pr "@[<v 0>Checking for side conditions on the left@; @[<v 0>";
  let phi_l = phi_proj proj_l in
          
  Printer.pr "@]@,Checking for side conditions on the right@; @[<v 0>";
  let phi_r = phi_proj proj_r in
  Printer.pr "@]@]@;";

  (* Removing duplicates. We already did that for occurrences, but
     only within phi_l and phi_r, not across both *)
  let cstate = Reduction.mk_cstate contx.table in
  let phis =
    Utils.List.remove_duplicate
      (Reduction.conv cstate) (phi_l @ phi_r)
  in

  let phi = Term.mk_ands ~simpl:true phis in
  let new_t = subst_name xc c_len cc in
  let new_biframe = List.rev_append before (new_t::after) in
  [ES.set_reach_conclusion phi s; ES.set_equiv_conclusion new_biframe s]

  

(*------------------------------------------------------------------*)
let indcca1_tac args =
  match args with
  | [Args.Int_parsed i] -> wrap_fail (indcca1 i)
  | _ -> LT.bad_args ()


let () =
  T.register_general "cca1"
   ~pq_sound:true
   (LT.gentac_of_etac_arg indcca1_tac)