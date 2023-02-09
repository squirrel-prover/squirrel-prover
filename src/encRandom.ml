(** Auxiliary functions to generate random freshness conditions. 
    Built using NameOccs, used for int-ctxt and ind-cca. *)
open Term
open Utils

module PathCond = Iter.PathCond

module Args = TacticsArgs
module L = Location
module SE = SystemExpr
module NO = NameOccs

module TS = TraceSequent

module Hyps = TS.LocalHyps

module Name = NameOccs.Name

type sequent = TS.sequent

type lsymb = Theory.lsymb

module MP = Match.Pos
module Sp = MP.Sp

(*------------------------------------------------------------------*)
let soft_failure = Tactics.soft_failure


(** Auxiliary function to check if a name with the same 
   symbol as n occurs in t (without expanding macros) *)
let rec has_name (n:Name.t) (t:term) : bool =
  match t with
  | Name (nn, _) when nn = n.symb -> true
  | _ -> Term.texists (has_name n) t
 

(** Occurrence of a ciphertext enc(m,r,k1)
    with some key k1 with the same symbol as kcoll.
    Additionally in 'b we store (m,r,k1,kcoll)
    so that we won't need to compute them again later. *)
type ctxt_aux = { 
  ca_m     : term ; 
  ca_r     : Name.t ; 
  ca_k1    : Name.t ; 
  ca_kcoll : Name.t ;
}

type ctxt_occ = (term, ctxt_aux) NO.simple_occ
type ctxt_occs = ctxt_occ list

type ectxt_occ = (term, ctxt_aux) NO.ext_occ
type ectxt_occs = ectxt_occ list
    

(** Occurrence for c = enc(m, r, k1), colliding with ccoll which uses kcoll. 
    c is meant to syntactically be a ciphertext,
    ccoll not necessarily (which is why it's useful
    to store its key separately) *)
let mk_ctxt_occ
    (c:term) (ccoll:term)
    (m:term) (r:Name.t)
    (k1:Name.t) (kcoll:Name.t)
    (fv:Vars.vars) (cond:terms) (ot:NO.occ_type) (st:term) :
  ctxt_occ =
  let fv, sigma = refresh_vars fv in
  let cond = List.map (Term.subst sigma) cond in
  let ot = NO.subst_occtype sigma ot in
  let c = Term.subst sigma c in
  let m = Term.subst sigma m in
  let r = Name.subst sigma r in
  let k1 = Name.subst sigma k1 in
  let st = subst sigma st in
  NO.mk_simple_occ
    c ccoll
    {ca_m=m; ca_r=r; ca_k1=k1; ca_kcoll=kcoll}
    fv cond ot st


(** Randomness occurrence.
    'a is Name.t, for the name r' which is the occurrence
    'b contains a ectxt_occ, which is the occ enc(m,r,k1) where
    the r that r' collides with was found,
    and optionally a pair [(m',k'):term * Name.t] for the
    case where r' was found in enc(m',r',k').
*)
type rand_occ = (Name.t, (ectxt_occ * (term * Name.t) option)) NO.simple_occ
type rand_occs = rand_occ list

let mk_rand_occ
    (r:Name.t) (co:ectxt_occ) (p:(term * Name.t) option)
    (cond:terms) (fv:Vars.vars) (ot:NO.occ_type) (st:term) : rand_occ 
  =
  let fv, sigma = refresh_vars fv in
  let r = Name.subst sigma r in
  let p = Option.map (fun (m,k) -> subst sigma m, Name.subst sigma k) p in
  let cond = List.map (subst sigma) cond in
  let ot = NO.subst_occtype sigma ot in
  let st = Term.subst sigma st in
  let rcoll = NO.(co.eo_occ.so_ad.ca_r) in 
  NO.mk_simple_occ r rcoll (co, p)
    (fv @ (co.eo_occ.so_vars)) (* add the vars of co so they are
                                  quantified as well *)
    (cond @ (co.eo_occ.so_cond)) (* add the condition so it is treated
                                    just like r's condition *)
    ot st


(*------------------------------------------------------------------*)
(** Look for occurrences using NameOccs *)

type dec_allowed = Allowed | NotAllowed | NotAbove of Name.t

(** Checks whether decrypting a term with subterms ts is allowed *)
let is_dec_allowed (da:dec_allowed) (ts:Term.terms) : bool =
  match da with
  | Allowed -> true
  | NotAllowed -> false
  | NotAbove xc -> List.for_all (fun t -> not (has_name xc t)) ts

(** Finds occs of k, except those that are
    - in enc key position (if pkf = None)
    - in pub key position (if pkf <> None)
    - in dec key position depending on dec_allowed:
      -> if dec_allowed = Allowed: ignore these occs
      -> if dec_allowed = NotAllowed: count these occs
      -> if dec_allowed = NotAbove x: ignore these occs, unless x occurs in
          the ciphertext or the indices of the decryption key
    - under a hash, if hashf <> None
      (this is a special case only used for Charlie's sus assumption).
    Also finds all occs of names in rs, in any position. 
    returns additionally all occs of ciphertexts
    encrypted with (potentially) k, when pkf = None
    (for pub key encryption there is no integrity guarantee,
     so no need to collect the ciphertexts) *)
let get_bad_occs_and_ciphertexts
    (env : Env.t)            (* initial environment  *)
    (k:Name.t) (* key k to look for *)
    (rs:Name.t list) (* randoms to look for *)
    (c:term) (* ciphertext c in dec(c,k) <> fail *)
    (enc_f:Symbols.fname) (* encryption function *)
    (dec_f:Symbols.fname) (* decryption function *)
    ?(hash_f:Symbols.fname option=None) (* hash function,
                                   when one is defined together w/ enc *)
    ?(pk_f:Symbols.fname option=None) (* public key function, when
                                         using asymmetric encryption *)
    ~(dec_allowed:dec_allowed)
    (retry_on_subterms : (unit -> NO.n_occs * ctxt_occs))
    (rec_call_on_subterms :
       (fv:Vars.vars ->
        cond:terms ->
        p:MP.pos ->
        info:NO.expand_info ->
        st:term ->
        term ->
        NO.n_occs * ctxt_occs))
    ~(info:NO.expand_info)
    ~(fv:Vars.vars)
    ~(cond:terms)
    ~(p:MP.pos)
    ~(st:term)
    (t:term) 
  : NO.n_occs * ctxt_occs =
  (* handles a few cases, using rec_call_on_subterm for rec calls,
     and calls retry_on_subterm for the rest *)
  (* only use this rec_call shorthand if the parameters don't change! *)
  let rec_call = (* rec call on a list *)
    List.flattensplitmap (rec_call_on_subterms ~fv ~cond ~p ~info ~st)
  in
  let env =
    Env.update ~vars:(Vars.add_vars (Vars.Tag.global_vars ~const:true fv) env.vars) env
  in
  match t with
  | _ when HighTerm.is_ptime_deducible ~const:`Exact ~si:false env t -> ([],[])
                                                         
  | Var v ->
    soft_failure
      (Tactics.Failure (Fmt.str "terms contain a non-ptime variable: %a" Vars.pp v))

  (* a name with the same symbol as k or one of the rs *)
  | Name (_, nargs) as n when
      Name.exists_name (Name.of_term n) (k::rs) ->
    (* occurrences for n itself *)
    let occs1 =
      NO.find_name_occ (Name.of_term n) (k::rs) fv cond (fst info) st
    in
    (* rec call on the arguments *)
    let occs2, accs2 = rec_call nargs in
    occs1@occs2, accs2


  (* encryption with k: allowed when with a random *)
  (* only relevant in the symmetric case: for asymmetric enc,
     - k must be under pk anyway,
     - the randomness doesn't have to be a name,
     - we don't record the ciphertext,
     so just recursing works. *)
  | Fun (f, _, [Tuple [m; Name _ as r; Name (ksb', kargs') as k']]) 
    when pk_f = None && enc_f = f && k.symb.s_symb = ksb'.s_symb -> 
    (* look in m and in r (this automatically includes the args of r) *)
    (* also look in the args of k' *)
    let occs1, accs1 = rec_call (m::r::kargs') in
    (* don't forget to check if k' itself is in rs *)
    let occs2 = NO.find_name_occ (Name.of_term k') rs fv cond (fst info) st in
    ( occs1 @ occs2,
      accs1 @
      [mk_ctxt_occ t c m (Name.of_term r) (Name.of_term k') k
         fv cond (fst info) st] )


  (* decryption with k when allowed -- no occ for the key. *)
  (* is the same regardless of sym/asym encryption *)
  (* for int-ctxt: normally decryption is not allowed, there is only
     an oracle to check dec ≠ fail, but since when dec ≠ fail the attacker
     can compute the decryption himself, allowing a full dec oracle
     is the same *)
  | Fun (f, _, [Tuple [c; Name (ksb',kargs') as k']]) 
    when dec_f = f && k.symb.s_symb = ksb'.s_symb && is_dec_allowed dec_allowed (c::kargs') ->
    (* look in c and the args of k' *)
    let occs1, accs1 = rec_call (c :: kargs') in
    (* there's also the case where k' is one of the forbidden rs *)
    let occs2 = NO.find_name_occ (Name.of_term k') rs fv cond (fst info) st in
    occs1@occs2, accs1

  (* when a pk is defined: k may appear under pk (but rs may not) *)
  | Fun (f, _, [Name (_,kargs') as k'])
    when pk_f = Some f  ->
    (* rec call on the args of k' *)
    let occs1, accs1 = rec_call kargs' in
    (* k'= k is allowed, but still check if k' is an rs *)
    let occs2 = NO.find_name_occ (Name.of_term k') rs fv cond (fst info) st in
    occs1@occs2, accs1
    

  (* hash oracle: when enc has an associated hash function,
     we discard bad occurrences of k under any hash with any key
     (but keep the ciphertexts) *)
  | Fun (f, _, [Tuple [m; Name _ as k']])
    when hash_f = Some f  ->
    (* look in m and k' (k is not a hash key, it should not be used as k') *)
    let occs1, accs1 = rec_call [m] in
    let occs2, accs2 = rec_call [k'] in        
    (* discard occurrences from m that are not in rs
       (k is allowed under hash, but not the rs) *)
    let occs1 =
      List.filter (fun (o:NO.n_occ) -> List.mem (o.so_coll) rs) occs1
    in
    occs1@occs2, accs1@accs2

  | _ -> retry_on_subterms ()




(** Look for bad uses of the randoms r from the list of
    ciphertexts occurrences enc(m,r,k1). 
    ie - if r occurs somewhere not as r' in enc(m',r', k'):
           bad occ if k1 = k and r' = r
    - if r occurs as r' in enc(m',r',k'):
           bad occ if k1 = k and r' = r and (m' <> m or k' <> k).
    Only used for symmetric encryption: for asym enc, the adversary
    has the public key and can thus encrypt anything *)
let get_bad_randoms
    (env : Env.t)
    (k:Name.t)
    (cs:ectxt_occs)
    (enc_f:Symbols.fname) (* encryption function *)
    (retry_on_subterms : (unit -> NO.n_occs * rand_occs))
    (rec_call_on_subterms :
       (fv:Vars.vars ->
        cond:terms ->
        p:MP.pos ->
        info:NO.expand_info ->
        st:term ->
        term ->
        NO.n_occs * rand_occs))
    ~(info:NO.expand_info)
    ~(fv:Vars.vars)
    ~(cond:terms)
    ~(p:MP.pos)
    ~(st:term)
    (t:term) 
  : NO.n_occs * rand_occs =
  (* handles a few cases, using rec_call_on_subterm for rec calls,
     and calls retry_on_subterm for the rest *)
  (* only use this rec_call shorthand if the parameters don't change! *)
  let rec_call = (* rec call on a list *)
    List.flattensplitmap (rec_call_on_subterms ~fv ~cond ~p ~info ~st)
  in

  let env =
    Env.update ~vars:(Vars.add_vars (Vars.Tag.global_vars ~const:true fv) env.vars) env
  in
  match t with
  | _ when HighTerm.is_ptime_deducible ~const:`Exact ~si:false env t -> ([],[])

  | Var v ->
    soft_failure
      (Tactics.Failure (Fmt.str "terms contain a non-ptime variable: %a" Vars.pp v))

  (* r' found on its own is a bad occ if it is one of the r in enc(m, r, k1) *)
  | Name (_, rargs') as r' ->
    let rn' = Name.of_term r' in
    let oaccs1 =
      List.filter_map
        (fun (c_eocc:ectxt_occ) ->
           let c_occ = c_eocc.eo_occ in
           let r = c_occ.so_ad.ca_r in
           if r.symb.s_symb = rn'.symb.s_symb then
             Some 
               (NO.mk_nocc rn' r fv cond (fst info) st,
                mk_rand_occ rn' c_eocc None cond fv (fst info) st)
               (* we also generate a nocc with just the name.
                  We won't use it to generate conditions, it's here only
                  so that NameOccs prints it. not very pretty… *)
           else
             None)
        cs
    in
    let occs1, accs1 = List.split oaccs1 in
    (* also rec check in the arguments of r' *)
    let occs2, accs2 = rec_call rargs' in
    occs1@occs2, accs1@accs2

  (* r' found in enc(m',r',k') when k' potential collision with k *)
  (* (if k, k' have different symbols the previous case will apply) *)
  | Fun (f, _, [Tuple [m'; Name (_, rargs') as r'; Name (ksb',_) as k']])
    when enc_f = f && ksb'.s_symb = k.symb.s_symb ->
    let rn' = Name.of_term r' in
    let kn' = Name.of_term k' in
    (* look for bad occs in m' and in k' (k' could be a forbidden r) *)
    (* also look in the args of r' *)
    let occs1, accs1 = rec_call (m' :: k' :: rargs') in
    (* and add the occurrences for r': all the ciphertexts occs that use
       a r with the same symbol as r' *)
    let oaccs2 =
      List.filter_map
        (fun (c_eocc:ectxt_occ) ->
           let c_occ = c_eocc.eo_occ in
           let r = c_occ.so_ad.ca_r in
           if r.symb.s_symb = rn'.symb.s_symb then
             Some 
               (NO.mk_nocc rn' r fv cond (fst info) st,
                mk_rand_occ rn' c_eocc (Some (m', kn')) cond fv (fst info) st)
           else
             None)
        cs
    in
    let occs2, accs2 = List.split oaccs2 in
    occs1 @ occs2, accs1 @ accs2
    
  | _ -> retry_on_subterms ()




(** Constructs the formula expressing that a ciphertext occurrence
    c'=enc(m',r',k1) is indeed in collision with c, and k1 with k.
    used for integrity: if dec(c, k) succeeds, then c must be
    equal to (one of the) c'=enc(m',r',k1) for which k1 = k.
    (note that c is not necessarily syntactically an encryption with k,
    so c = c' is not sufficient: it doesn't necessarily mean that k = k1) *)
let ciphertext_formula
    ~(negate : bool)
    (c':term)
    (c:term)
    (ca:ctxt_aux)
    : term =
  let {ca_m = m'; ca_r = r'; ca_k1 = k1; ca_kcoll = k} = ca in
  let () = (* sanity check: the r', m', k' in ca match those in c' *)
    match c' with
    | Fun (_, _, [Tuple [m''; Name _ as r''; Name _ as k1']])
      when m'' = m' && 
           Name.of_term r'' = r' && 
           Name.of_term k1' = k1 && 
           k1.symb.s_symb = k.symb.s_symb ->
      ()
    | _ -> assert false
  in
  if not negate then 
    mk_and ~simpl:true
      (mk_eq ~simpl:true c c')
      (mk_eqs ~simpl:true k.args k1.args)
  else
    mk_or ~simpl:true
      (mk_not ~simpl:true (mk_eq ~simpl:true c c'))
      (mk_neqs ~simpl:true k.args k1.args)



                                          
(** Constructs the formula expressing that an occurrence of a random r'
    is indeed a bad occurrence of the r from the ctxt_occ enc(m,r,k1),
    given that the key we're interested in is k:
    - if r' was found in enc(m',r',k'):
       phi_time(r) && k1 = k && r' = r && (k' <> k || m' <> m)
      or the negative phi_time(r) => k1 = k => r' = r => k' = k && m' = m
    - if r' was found directly:
       phi_time(r) && k1 = k && r' = r
      or the negative phi_time(r) => k1 = k => r' = r => false.
      note that it does not include the phi_time for r',
      as this is handled by NameOccs.
      similarly, no need to worry about the conditions or vars,
      as they were all added to the cond by mk_rand *)
let randomness_formula
    ?(use_path_cond = false)
    ~(negate : bool)
    (r':Name.t)
    (r:Name.t)
    ((eco, omk): (ectxt_occ * (term * Name.t) option))
  (* eco: occ where r was, omk = option (m',k') *)
  : term 
  =
  let co = eco.eo_occ in
  let {ca_m=m; ca_r=rr; ca_k1=k1; ca_kcoll=k} = co.so_ad in
  assert (r = rr); (* sanity check *)
  let phi_time = (* phi_time(r) *)
    match co.so_occtype with
    | EI_direct -> mk_true
    | EI_indirect a -> 
      let path_cond = if use_path_cond then eco.eo_path_cond else PathCond.Top in
      NO.time_formula ~path_cond a eco.eo_source_ts
  in 
  let phi_k = mk_eqs ~simpl:true k1.args k.args in
  let phi_r = mk_eqs ~simpl:true r'.args r.args in
  let phi_km' =
    match omk, negate with
    | None, false -> mk_true
    | None, true -> mk_false
    | Some (m', k'), false ->
      mk_or ~simpl:true
        (mk_neqs ~simpl:true k'.args k.args)
        (mk_neq ~simpl:true  m' m)
    | Some (m', k'), true ->
      mk_and ~simpl:true
        (mk_eqs ~simpl:true k'.args k.args)
        (mk_eq ~simpl:true m' m)
  in
  if not negate then
    mk_ands ~simpl:true [phi_time; phi_k; phi_r; phi_km']
  else
    mk_impls ~simpl:true [phi_r; phi_k; phi_time] phi_km'


