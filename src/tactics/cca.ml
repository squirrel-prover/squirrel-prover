(* IND-CCA1 equiv tactic *)
open Squirrelcore
open Term
open Utils
open Ppenv

module Args = TacticsArgs
module L = Location
module SE = SystemExpr
module ES = EquivSequent
module LT = LowTactics
module T = ProverTactics

type sequent = ES.sequent

module O = Occurrences
module RO = RandomnessOccurrences
module Name = O.Name
type name = Name.t


(*------------------------------------------------------------------*)
let wrap_fail = LT.EquivLT.wrap_fail
let soft_failure = Tactics.soft_failure


module EOC = RO.EncryptionOC
module EOS = RO.EncryptionOS
module EOF = RO.EncryptionOF
let mk_simple_occ = EOS.EO.SO.mk_simple_occ


module ROC = RO.RandomnessOC
module ROS = RO.RandomnessOS
module ROF = RO.RandomnessOF



(*------------------------------------------------------------------*)
(* Look for occurrences using the Occurrences module *)

(** A [EOS.f_fold_occs] function.
    Looks for
    1) bad occurrences of the key [k]: places where a key with the same symbol
    as [k] is used other than in key position, ie
    - as enc key, if pkf = None (symmetric case)
    - as pub key, if pkf <> None (asymmetric case)
    - as dec key: as specified by the dec_allowed argument

    2) bad occurrences of the random [r]: places where a name with
    the same symbol occurs (in any position)

    3) occurrences of ciphertexts, with a key that has
    the same symbol as [k] (only in the symmetric case, ie if pk <> None.)

    2 may be surprising: one might expect that [r] is allowed to occur
    as long as it is as a random in an encryption with the same key,
    ie in [enc(m', r, k')] with [m = m' /\ k = k'].
    The issue is then that we would need to ensure that no decryption with [k]
    is performed above that ciphertext when [m = m' /\ k = k'] holds, which
    we do not check. So we just reject any occurrence of [r], which is sound.
    Note that occurrences where [m'] and [k'] are syntactically [m] and [k]
    are fine, as they will be all be replaced with a name. *)
let get_bad_occs
    (env : Env.t)
    ~(k : name)
    ~(r:name) 
    ~(enc_f : Symbols.fname) (* encryption function *)
    ~(dec_f : Symbols.fname) (* decryption function *)
    ?(pk_f : Symbols.fname option=None) (* public key function. *)
    ~(da : RO.dec_allowed)
    ~(retry : unit -> EOS.simple_occs)
    ~(rec_call : O.pos_info -> Term.term -> EOS.simple_occs)
    (info : O.pos_info)
    (t : term) 
  : EOS.simple_occs
  =
  (* handles a few cases, using rec_call for rec calls on subterms,
     and calls retry for the rest *)

  (* variables quantified above the current point are considered constant,
     so we add them to the env used for "is_ptime_deducible" *)
  let env =
    Env.update
      ~vars:(Vars.add_vars
               (Vars.Tag.global_vars ~const:true info.pi_vars) env.vars)
      env
  in
  match t with
  | _ when HighTerm.is_ptime_deducible ~si:false env t -> []
  (* SI not needed here *)

  (* non ptime deterministic variable -> forbidden *)
  (* (this is where we used to check variables
     were only timestamps or indices) *)
  | Var v ->
    soft_failure
      (Tactics.Failure
         (Fmt.str "terms contain a non-ptime variable: %a" Vars.pp v))

  (* a name -> check if it is an occurrence of the key or random *)
  | Name (_, nargs) as n ->
    let n = Name.of_term n in
    (* find out if k or r have the same symbol as n *)
    (* (as a list: in case both have the same symbol, two occurrences) *)
    let l = Name.find_name n [k; r] in
    (* generate occurrences for these, and recurse on nargs *)
    let occs = List.concat_map (rec_call info) nargs in
    let oc = List.map (fun x ->
        mk_simple_occ
          ~content:(BadName n)
          ~collision:(BadName x)
          ~data:NoData
          ~vars:info.pi_vars
          ~cond:info.pi_cond
          ~typ:info.pi_occtype
          ~sub:info.pi_subterm
          ~show:Show)
        l
    in
    oc @ occs

  (* occurrence of the public key (for the asymmetric case only) *)
  | App (Fun (f, _), [tk']) when pk_f = Some f -> (* pk(tk') *)
    begin
      match O.expand_macro_check_all (O.get_expand_info info) tk' with
      | Name (ks', kargs') when r.symb.s_symb <> ks'.s_symb -> 
        (* pk(k' kargs'): we ignore it, even if k' = k, 
           as long as k' does not have the same symbol as r *)
        List.concat_map (rec_call info) kargs'

      | Name (_, kargs') as k' -> (* pk(r kargs') *)
        let k' = Name.of_term k' in
        let occs = List.concat_map (rec_call info) kargs' in
        let oc = mk_simple_occ 
            ~content:(BadName k') 
            ~collision:(BadName r)
            ~data:NoData 
            ~vars:info.pi_vars 
            ~cond:info.pi_cond 
            ~typ:info.pi_occtype 
            ~sub:info.pi_subterm
            ~show:Show
        in
        oc :: occs

      | _ -> retry () (* otherwise look in tk' *)
    end


  (* encryption w/ a name that could be the right key *)
  (* only relevant in the symmetric case. 
     in the asymmetric case, we do not record ciphertexts to check randomness
     conditions later, and the encryption key is under pk_f anyway. *)
  (* in the symmetric case: an actual random must be used as random *)
  (* we record this ciphertext occurrence, but allow the key *)
  | App (Fun (f, _), [Tuple [m; Name _ as r'; Name (ksb', kargs') as k']])
    when f = enc_f && pk_f = None && k.symb.s_symb = ksb'.s_symb ->
    (* look in m, r', kargs' *)
    let occs = List.concat_map (rec_call info) (m :: r' :: kargs') in
    (* we do not care if k' is k, but don't forget to also check whether 
       k' could be r *)
    let k' = Name.of_term k' in
    let occs =
      if k'.symb.s_symb = r.symb.s_symb then 
        (mk_simple_occ
           ~content:(BadName k')
           ~collision:(BadName r)
           ~data:NoData 
           ~vars:info.pi_vars 
           ~cond:info.pi_cond 
           ~typ:info.pi_occtype 
           ~sub:info.pi_subterm
           ~show:Show) :: occs
      else occs
    in
    (* and record the ciphertext *)
    let oc = mk_simple_occ
        ~content:(Ciphertext t)
        ~collision:NoCipher
        ~data: 
          (DataCiphertext {msg=m; 
                           rand=Name.of_term r'; 
                           key=k'; 
                           keycoll=k})
        ~vars:info.pi_vars 
        ~cond:info.pi_cond 
        ~typ:info.pi_occtype 
        ~sub:info.pi_subterm
        ~show:Hide (* we don't want to print these *)
    in
    oc :: occs

  (* decryption w/ a name that could be the right key *)
  (* we allow it only if the conditions from the [dec_allowed] flag are met *)
  | App (Fun (f, _), [Tuple [c; Name (ksb', kargs') as k']])
    when f = dec_f && k.symb.s_symb = ksb'.s_symb &&
         RO.is_dec_allowed da (c :: kargs') ->
    (* still look in c, kargs' *)
    let occs = List.concat_map (rec_call info) (c :: kargs') in
    (* we do not care if k' is k, but don't forget to also check whether 
       k' could be r *)
    let k' = Name.of_term k' in
    if k'.symb.s_symb = r.symb.s_symb then 
      (mk_simple_occ
         ~content:(BadName k')
         ~collision:(BadName r)
         ~data:NoData 
         ~vars:info.pi_vars 
         ~cond:info.pi_cond 
         ~typ:info.pi_occtype 
         ~sub:info.pi_subterm
         ~show:Show) :: occs
    else occs

  | _ -> retry ()





(*------------------------------------------------------------------*)
(** {2 IND-CCA parameters } *)
(** Utilities to find the parameters (which encryption symbol, which
    challenge ciphertext, etc.) when applying ind-cca *)

(** Replaces any name with the same symbol as n with tsub in t.
    Use at your own risks when n has arguments
    (will not recursively look in them) *)
let rec subst_name (n:name) (tsub:term) (t:term) : term =
  match t with
  | Name (n', _) when n' = n.symb -> tsub
  | _ -> Term.tmap (subst_name n tsub) t


(** Checks that there is no diff or binder in t above any name
    with the same symbol as n.
    Does not unfold any macro (meant to be used after rewriting
    in indcca_param, so we know that no occurrence of n can be
    under a macro). very inefficient but it shouldn't matter too much. *)
let rec check_nodiffbind (n:name) (t:term) : bool =
  if not (Name.has_name n t) then true
  else
    match t with
    | Diff (Explicit _) -> false
    | _ when Term.is_binder t -> false
    | _ -> Term.tforall (check_nodiffbind n) t


(** Returns true iff f is a symmetric or asymmetric encryption function. *)
let is_enc (table:Symbols.table) (f:Symbols.fname) : bool =
  Symbols.OpData.(
    is_abstract_with_ftype f AEnc table ||
    is_abstract_with_ftype f SEnc table
  )

(** Returns true iff t contains an encryption function.
    Does not unfold macros. *)
let rec has_enc (table:Symbols.table) (t:term) : bool =
  match t with
  | Term.Fun (f, _) when is_enc table f -> true
  | _ -> Term.texists (has_enc table) t


(** Checks that each term ti in ts is f(argsi) for the same f,
    if so returns f and the list [args1;…;argsn].
    Does the same if each ti is Tuple(argsi)
    (but returns None as the function in that case). *)
let same_head_function (ts:Term.terms) :
  ((Symbols.fname * applied_ftype) option * Term.terms list) option =
  if ts = [] then Some (None, [])
  else
    let exception NotTheSame in
    try
      let f, args0 = match List.hd ts with
        | App (Fun (fs, ft), args) -> Some (fs, ft), args
        | Tuple args -> None, args
        | _ -> raise NotTheSame
      in
      let res =
        List.map
          (fun t -> match t with
             | App (Fun (fs, ft), args) when f = Some (fs, ft) ->
               args
             | Tuple args when f = None ->
               args
             | _ -> raise NotTheSame)
          (List.tl ts)
      in
      Some (f, args0 :: res)
    with
      NotTheSame -> None


(* TODO this is very ad hoc, do we have a generic mechanism for this?
   If not, do we want one? *)
(** Moves any diff that is above an encryption function down
    as much as possible, stopping once it gets under the enc.
    Also moves diffs under tuples. *)
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


(** Finds the parameters of the cca application *)
let indcca_param
    ~(loc:L.t)
    (t:term)    (* element in the goal where we want to apply cca *)
    (s:sequent)    
  : indcca_param
  = 
  let table = ES.table s in
  let secontx = ES.system s in
  let sys = ES.get_system_pair s in 
  let hyps = ES.get_trace_hyps s in
  let t = move_diff table t in (* move the diffs under the enc,
                                  as much as possible *)

  (* rw_rule trying to rewrite an instance of f(M,R,K)
     (where M, R, K are fresh variables) into a fresh name X *)
  (* returns the rule, the updated table with the new declarations, and
     the fresh name X *)
  (* use "Tuple [M;R;K]" to retrieve the value of vars once instantiated *) 
  let mk_rewrule
      (f:Symbols.fname)
      (cty:Type.ty) (mty:Type.ty) (rty:Type.ty) (kty:Type.ty) :
    Rewrite.rw_rule * Symbols.table * Name.t =
    (* type for name X: the type of the ciphertext *)
    let n_fty = Type.mk_ftype [] [] cty in

    (* adding X to the table *)
    let xcdef = Symbols.Name {n_fty} in
    let s = L.mk_loc L._dummy "X" in
    let table, xcs =
      Symbols.Name.declare ~approx:true table s ~data:xcdef
    in

    (* constructing the name X, and the variables M, R, K *)
    let xc = Name.{symb=Term.mk_symb xcs cty; args=[]} in
    let xm = Vars.make_fresh mty "M" in
    let xr = Vars.make_fresh rty "R" in
    let xk = Vars.make_fresh kty "K" in

    (* the rewrite rule *)
    {
     rw_params = Params.empty;
     rw_system = SE.to_arbitrary sys; (* rewrite in the pair *)
     rw_vars   = Vars.Tag.local_vars [xm; xr; xk]; (* local information,
                                                      since we allow to
                                                      match diff operators *)

     rw_conds  = [mk_eq ~simpl:false (* a condition, to retrieve later on
                                        the values that M, R, K matched *)
                    (mk_tuple [mk_var xm; mk_var xr; mk_var xk])
                    (Library.Prelude.mk_witness table
                       ~ty_arg:(Type.tuple [mty; rty; kty]))];
     rw_rw     = (mk_fun_tuple table f [mk_var xm; mk_var xr; mk_var xk]),
                 (Name.to_term xc);
     rw_kind   = GlobalEq;
     rw_bound = Concrete.Glob;
    },
    (* TODO: Concrete: Probably something to do to create a bounded rewrite *)
    table,
    xc
  in

  (* go through all encryption functions, try to find one for which
     a ciphertext appears in the term *)
  let res = 
    let exception Found of (Symbols.fname * Rewrite.rw_res * 
                            Symbols.table * name)
    in
    try 
      Symbols.Operator.iter
        (fun f _ -> (* for all functions:*)
           if is_enc table f then
             (* f is an encryption: try to find a ciphertext *)
             let fty = Symbols.OpData.ftype table f in
             let cty = fty.fty_out in
             let mty, rty, kty =
               match fty.fty_args with
               | [Type.Tuple [x;y;z]] -> x,y,z
               | _ -> assert false
             in

             let rule, table, xc = mk_rewrule f cty mty rty kty in
             let res =
               Rewrite.rewrite
                 table (ES.params s)
                 Vars.empty_env (* only local variables,
                                   hence [env] is useless here *)
                 secontx InSequent hyps TacticsArgs.Once
                 rule
                 Equiv.(Global (Atom (Equiv {terms = [t]; bound = None})))
                 (* TODO: Concrete: Probably something to do to create
                    a bounded goal *)
             in
             begin
               match res with
               | Rewrite.RW_Result rr -> raise (Found (f, rr, table, xc))
               | _ -> ()
             end)
        table;
      (* no ciphertext was found: error *)
      soft_failure ~loc (Tactics.Failure "no ciphertext found")
    with 
    | Found x -> x
  in

  match res with 
  | enc_f, (ccc, [(_, l)]), table, xc ->
    let dec_f, pk_f = (* get the associated dec and pk functions *)
      match Symbols.OpData.get_abstract_data enc_f table with
      | _, [dec_f] -> (* sym enc *)
        (* sanity checks: everything has the correct type *)
        assert Symbols.OpData.(is_abstract_with_ftype enc_f SEnc table);
        assert Symbols.OpData.(is_abstract_with_ftype dec_f SDec table);
        dec_f, None
      | _, [dec_f; pk_f] -> (* asym enc *)
        (* sanity checks: everything has the correct type *)
        assert Symbols.OpData.(is_abstract_with_ftype enc_f AEnc      table);
        assert Symbols.OpData.(is_abstract_with_ftype dec_f ADec      table);
        assert Symbols.OpData.(is_abstract_with_ftype pk_f  PublicKey table);
        dec_f, (Some pk_f)
      | _ -> assert false
    in

    (* get the context around the ciphertext *)
    let cc =
      match Equiv.any_to_equiv ccc with
      | Equiv.(Atom (Equiv {terms = [cc]; bound = None})) -> cc
      (* TODO: Concrete: Probably something to do to create a bounded goal *)
      | _ -> assert false (* cannot happen given the term we constructed *)
    in

    (* get the content of variables from the conditions *)
    (* extract the last thing in l, in case additional conditions
       were collected *)
    (* also remove universally quantified variables that may have been
       introduced in the condition. Note that in that case, m, r, k will
       contain free variables. This is not an issue: in that case there must 
       be a quantifier above the ciphertext we found, and thus the tactic will
       fail anyway later on *)
    let l = snd (decompose_impls_last (snd (decompose_forall l))) in
    let m, r, k =
      match l with
      | Term.(App (Fun (ff, _), [Tuple [m; r; k]; _])) when
          ff = Term.f_eq ->
        m,r,k
      | _ -> assert false
    in

    (* only thing left is checking there's no diff or binders
       above N in cc *)
    if not (check_nodiffbind xc cc) then 
      soft_failure ~loc
        (Tactics.Failure 
           "no diff or binder allowed above the ciphertext for cca");
    (* return the parameters *)
    {ip_enc=enc_f; ip_dec=dec_f; ip_pk=pk_f; ip_context=cc;
     ip_cname=xc; ip_plain=m; ip_rand=r; ip_key=k; ip_table=table}

  | _ -> assert false




(*------------------------------------------------------------------*)
(** {2 Conditions for IND-CCA} *)


(** Constructs a formula expressing that in the [frame] + the [context]
    around the challenge ciphertext + the plaintext [m], 
    the random [r], the key [k]:
    - no decryption with [k] is present above the ciphertext in the [context]
    - [k] is correctly used
    - the randomness [r] does not occur elsewhere
    - the other randoms are fresh (only used once).
      Note that the [context] contains a name standing in for the ciphertext.
      In the generated formulas, we instantiate it twice: once with the 
      actual ciphertext, once with the encryption of its length. 
      Indeed, the formula must hold on the real and ideal sides if we want to 
      apply ind-cca. 
      This function assumes everything (the [hyps], the terms)
      has already been projected,
      and is understood in [env.system.set]. *)
let phi_cca_one_system
    ~(use_path_cond : bool)
    ?(loc : L.t option)
    (hyps : Hyps.TraceHyps.hyps)
    (contx : Constr.trace_cntxt)
    (env : Env.t)
    (icp : indcca_param)
    (frame : terms)
  : Term.terms
  =

  (* sanity check: contx and env should agree *)
  assert (SE.equal0 env.system.set ((contx.system) :> SE.arbitrary));

  let ppe = default_ppe ~table:env.table () in

  (* Check that the random and key provided in icp are in fact names/pubkeys. *)
  let k, r = 
    match icp.ip_pk, icp.ip_key, icp.ip_rand with
    | None, (Name _ as k), (Name _ as r) -> (* sym enc: key is a name *)
      Name.of_term k, Name.of_term r
    | Some pk_f, App (Fun (pk_f',_), [Name _ as k]), (Name _ as r)
      when pk_f = pk_f' -> (* asym enc: key is a pk with the right pk_f *)
      Name.of_term k, Name.of_term r       
    | _ -> soft_failure ?loc
             (Tactics.Failure "Can only be applied on an encryption \
                               where the random and (secret) key are names.")
  in

  (* Printers for k and r *)
  let pp_kr ppf () = 
    Fmt.pf ppf "occurrences of %a and %a" (Name.pp ppe) k (Name.pp ppe) r in
  let pp_rand ppf () = Fmt.pf ppf "occurrences of randomness" in


  (* In the rare case where k and r have the same symbol,
     an additional proof obligation requires that they have
     different arguments. Note that the formula as written here only works
     because no binders are allowed above the ciphertext. *)
  let phis0 =
    if k.symb.s_symb = r.symb.s_symb then
      [mk_neqs ~simpl:true ~simpl_tuples:true k.args r.args]
    else
      []
  in

  (* Find bad occurrences of k and r, and all ciphertexts with k *)
  let get_bad_krc : da:RO.dec_allowed -> EOS.f_fold_occs = 
    get_bad_occs env ~k ~r 
      ~enc_f:icp.ip_enc ~dec_f:icp.ip_dec ~pk_f:icp.ip_pk
  in

  (* First: in the frame + m + kargs + rargs.
     here, decryption is allowed (we are before the challenge ciphertext) *)
  let occs_krc = 
    EOS.find_all_occurrences ~mode:Iter.PTimeNoSI ~pp_descr:(Some pp_kr)
      (get_bad_krc ~da:Allowed)
      hyps contx env
      (icp.ip_plain :: k.args @ r.args @ frame)
  in

  (* Then: in the context above the challenge ciphertext.
     There, decryption with k is allowed ONLY on subterms that do not contain
     the name which stands for the challenge *)
  let occs_krc' =
    EOS.find_all_occurrences ~mode:Iter.PTimeNoSI ~pp_descr:(Some pp_kr)
      (get_bad_krc ~da:(NotAbove icp.ip_cname))
      hyps contx env
      [icp.ip_context]
  in

  (* Split occurrences of k and r from the ciphertexts *)
  let occs_kr, occs_c =
    List.fold_left 
      (fun (occs_kr, occs_c) (occ:EOS.ext_occ) ->
         match occ.eo_occ.so_cnt with 
         | BadName _ -> occ::occs_kr, occs_c
         | Ciphertext _ -> occs_kr, occ::occs_c
         | _ -> assert false)
      ([],[])
      (occs_krc @ occs_krc')
  in

  (* Put them back in order. idk if that's really useful, it was just
     to keep the historical order *) 
  let occs_kr, occs_c = List.rev occs_kr, List.rev occs_c in

  (* We can now generate the formulas for all the bad name (k or r) occs. 
     We do not generate formulas for the ciphertexts occs: these are only used
     to check the randomness conditions afterwards. *)
  let phis_kr =
    List.map (EOF.occurrence_formula ~negate:true ~use_path_cond) occs_kr
  in

  (* We now search for bad use of all randoms used in occs_c *)
  let get_bad_randoms : ROS.f_fold_occs = 
    RO.get_bad_randoms env ~k ~enc_f:icp.ip_enc ~ciphertexts:occs_c
  in

  let occs_r =
    if icp.ip_pk = None then (* only in the symmetric case *)
      ROS.find_all_occurrences ~mode:PTimeNoSI ~pp_descr:(Some pp_rand)
        get_bad_randoms
        hyps contx env
        (icp.ip_context :: icp.ip_plain :: (Name.to_term k) :: r.args @ frame)
        (* in principle kargs (not k) should suffice: if k occurred as
           a random somewhere, a bad occ would have been generated for that 
           already *)
    else
      []
  in

  let phis_r = 
    List.map (ROF.occurrence_formula ~negate:true ~use_path_cond) occs_r
  in

  (* Finally, we apply the substitution to the name representing 
     the challenge ciphertext in the context *)
  (* IT ONLY WORKS because all variables in the ciphertext are bound in the env,
     not in binders, as we forbid binders above the ciphertext *)

  (* the ciphertext, and the ciphertext encrypting its length instead of m *)
  let c = 
    Term.(mk_fun icp.ip_table icp.ip_enc
            [mk_tuple [icp.ip_plain; icp.ip_rand; icp.ip_key]]) 
  in
  let c_len = 
    Term.(mk_fun icp.ip_table icp.ip_enc
            [mk_tuple 
               [Library.Prelude.mk_zeroes icp.ip_table (mk_len icp.ip_plain); 
                icp.ip_rand; 
                icp.ip_key]]) 
  in
  let phis = phis0 @ phis_kr @ phis_r in
  let phis =
    List.concat_map
      (fun x -> List.map (subst_name icp.ip_cname x) phis)
      [c; c_len]
  in 

  phis



(*------------------------------------------------------------------*)
(** Constructs a list of formulas whose conjunction expresses
    the conditions to apply ind-cca to a given challenge ciphertext
    (with the context, etc. specified in [icp]), after projecting on [proj].
    [hyps] are understood in [env], and all terms ([frame], etc) in
    [env.system.pair], which must be the system in [contx]. *)
let phi_cca_proj
    ~(use_path_cond : bool)
    ?(loc : L.t option)
    (hyps : Hyps.TraceHyps.hyps)
    (contx : Constr.trace_cntxt)
    (env : Env.t)
    (icp : indcca_param)
    (frame : terms)
    (proj : Projection.t)
  : Term.terms
  =

  let system = ((Utils.oget env.system.pair) :> SE.fset) in

  (* sanity check: contx and env should agree *)
  assert (SE.equal0 system contx.system);

  (* get the projected system and context
     in which terms are now to be understood *)
  let systemp = SE.project [proj] system in
  let contxp = { contx with system = systemp } in
  let infop = (O.EI_direct, contxp) in

  (* the new environment,
     where the generated formulas are to be understood:
     {set = proj of env.system.pair, pair = env.system.pair} *)
  let envp_context = {env.system with set=(systemp :> SE.arbitrary)} in
  let envp = Env.update ~system:envp_context env in

  (* keep what hypotheses we can *)
  let hypsp =
    Hyps.change_trace_hyps_context
      ~old_context:env.system
      ~new_context:envp.system
      ~vars:env.vars ~table:env.table
      hyps
  in

  (* project the parameters on proj *)
  let fp = Term.project1 proj in
  let efp x = O.expand_macro_check_all infop (fp x) in
  let framep = List.map (Term.project1 proj) frame in
  let icpp = {icp with ip_context = fp icp.ip_context;
                       ip_plain = fp icp.ip_plain;
                       ip_rand = efp icp.ip_rand;
                       ip_key = efp icp.ip_key; }
  in

  phi_cca_one_system 
    ~use_path_cond ?loc
    hypsp contxp envp icpp framep




(*------------------------------------------------------------------*)
(** {2 IND-CCA1 tactic} *)
(** Constructs the sequent where goal [i], when of the form [C[enc(m,r,k)]],
    is replaced with [C[enc(zeroes(m),r,k)]], and an additional proof
    obligation [phi] is created, which expresses the conditions for the 
    ind-cca reduction to hold. *)
let indcca1 (i:int L.located) (s:ES.sequent) : ES.sequents =

  let use_path_cond = false in
  let loc = L.loc i in

  let env = ES.env s in
  let pair_context = ES.mk_pair_trace_cntxt s in
  let proj_l, proj_r = ES.get_system_pair_projs s in

  if (ES.conclusion_as_equiv s).bound <> None then 
    soft_failure 
      (Tactics.GoalBadShape "IND-CCA does not handle concrete bounds.");

  let before, e, after = LT.split_equiv_conclusion i s in
  let biframe = List.rev_append before after in


  (* get the parameters, enforcing that
     e does not contain diffs or binders above the ciphertext.
     (at least the diff part could maybe be relaxed?) *)
  let icp = indcca_param ~loc e s in
  let pair_context_ex = {pair_context with table=icp.ip_table} in
  let env_ex = {env with table=icp.ip_table} in

  let phi_cca_p =
    phi_cca_proj ~use_path_cond ~loc 
      (ES.get_trace_hyps s) 
      pair_context_ex env_ex icp biframe
      (* FEATURE: allow the user to set [use_path_cond] to true *)
  in

  Printer.pr "@[<v 0>Checking for side conditions on the left@; @[<v 0>";
  let phi_l = phi_cca_p proj_l in
  Printer.pr "@]@,Checking for side conditions on the right@; @[<v 0>";
  let phi_r = phi_cca_p proj_r in
  Printer.pr "@]@]@;";

  (* Removing duplicates. We already did that for occurrences, but
     only within [phi_l] and [phi_r], not across both *)
  let phis =
    List.remove_duplicate (ES.Reduce.conv_term s) (phi_l @ phi_r)
  in

  let phi = Term.mk_ands ~simpl:true phis in

  (* The new term, with the idealised ciphertext *)
  let c_len = 
    Term.(mk_fun (ES.table s) icp.ip_enc
            [mk_tuple 
               [Library.Prelude.mk_zeroes (ES.table s) (mk_len icp.ip_plain); 
                icp.ip_rand; 
                icp.ip_key]]) 
  in
  let new_t = subst_name icp.ip_cname c_len icp.ip_context in
  let new_biframe = List.rev_append before (new_t::after) in

  (* the sequent for the new proof obligation. *)
  (* TODO: here we ask to prove phi_l & phi_r on [left, right].
     It would be more precise to have diff(phi_l, phi_r). *)
  let cca_sequent =
    ES.set_conclusion_in_context
      {env.system with set=(pair_context.system :> SE.arbitrary)}
      (Equiv.mk_reach_atom phi)
      s
  in
  [cca_sequent;
   ES.set_equiv_conclusion {terms = new_biframe; bound = None} s]



(*------------------------------------------------------------------*)
let indcca1_tac args =
  match args with
  | [Args.Term_parsed {pl_desc = Int i}] -> wrap_fail (indcca1 i)
  | _ -> LT.bad_args ()


let () =
  T.register_general "cca1"
    ~pq_sound:true
    (LT.gentac_of_etac_arg indcca1_tac)
