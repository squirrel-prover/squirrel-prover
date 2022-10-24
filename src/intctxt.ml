(* INT-CTXT trace tactic *)
open Term
open Utils

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

open LowTactics

(*------------------------------------------------------------------*)
let wrap_fail = TraceLT.wrap_fail
let soft_failure = Tactics.soft_failure
let hard_failure = Tactics.hard_failure


(* occurrence of a ciphertext enc(m,r,k1)
   with some key k1 with the same symbol as k. *)
(* additionally in 'b we store (m,r,k1,k)
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
    
(* occurrence for c = enc(m, r, k1), colliding with ccoll which uses kcoll *)
let mk_ctxt_occ
    (c:term) (ccoll:term)
    (m:term) (r:Name.t)
    (k1:Name.t) (kcoll:Name.t)
    (fv:Vars.vars) (cond:terms) (ot:NO.occ_type) (st:term) :
  ctxt_occ =
  let fv, sigma = refresh_vars `Global fv in
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


(* randomness occurrence *)
(* 'a is Name.t, for the name r' which is the occurrence
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
  let fv, sigma = refresh_vars `Global fv in
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
(* Look for occurrences using NameOccs *)

(** look for bad uses of the key, collect ciphertexts as well *)
let get_bad_occs_and_ciphertexts
    (k:Name.t) (* key k in dec(c,k) <> fail *)
    (c:term) (* ciphertext c in dec(c,k) <> fail *)
    (enc_f:Symbols.fname) (* encryption function *)
    (dec_f:Symbols.fname) (* decryption function *)
    ?(hash_f:Symbols.fname option=None) (* hash function,
                                   when one is defined together w/ enc *)
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
  match t with
  | Var v when not (Type.is_finite (Vars.ty v)) ->
    soft_failure
      (Tactics.Failure "can only be applied on ground terms")

  | Name (ksymb', _) as k' when ksymb'.s_symb = k.symb.s_symb ->
    [NO.mk_nocc (Name.of_term k') k fv cond (fst info) st],
    []

  (* could expand macros here. todo? *)
  (* encryption with k: allowed when with a random *)
  | Fun (f, _, [Tuple [m; Name (rsymb, _) as r; Name (ksymb', _) as k']]) 
    when enc_f = f && k.symb.s_symb = ksymb'.s_symb -> 
    (* look in m also *)
    let occs,accs = rec_call_on_subterms ~fv ~cond ~p ~info ~st m in
    (* don't forget the case where r itself is a bad occ of k *)
    let occ =
      if rsymb.s_symb = k.symb.s_symb then
        [NO.mk_nocc (Name.of_term r) k fv cond (fst info) st]
      else []
    in
    ( occs @ occ,
      accs @ 
      [mk_ctxt_occ t c m (Name.of_term r) (Name.of_term k') k fv cond (fst info) st] )

  (* "normal" int-ctxt only has an oracle to check dec ≠ fail, but
     when dec ≠ fail the attacker can compute the decryption himself,
     so a full dec oracle is the same *)
  (* decryption with k is allowed *)
  | Fun (f, _, [Tuple [c; Name (ksymb',_) as _k']]) 
    when dec_f = f && k.symb.s_symb = ksymb'.s_symb ->
    rec_call_on_subterms ~fv ~cond ~p ~info ~st c


  (* hash oracle: when enc has an associated hash function,
     we discard bad occurrences of k under any hash with any key
     (but keep the ciphertexts) *)
  | Fun (f, _, [Tuple [m; Name _ as _k']])
    when hash_f = Some f  ->
    let _, accs = rec_call_on_subterms ~fv ~cond ~p ~info ~st m in
    [], accs

  | _ -> retry_on_subterms ()



(** look for bad uses of the randoms r from the list of
    ciphertexts occurrences enc(m,r,k1) *)
(** ie - if r occurs somewhere not in enc(m',r', k'):
           bad occ if k1 = k and r' = r
    - if r occurs in enc(m',r',k'):
           bad occ if k1 = k and r' = r and (m' <> m or k' <> k) *)
let get_bad_randoms
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
  match t with
  | Var v when not (Type.is_finite (Vars.ty v)) ->
    soft_failure
      (Tactics.Failure "can only be applied on ground terms")

  (* r' found on its own is a bad occ if it is one of the r in enc(m, r, k1) *)
  | Name _ as r' ->
    let r_n' = Name.of_term r' in
    let accs =
      List.filter_map
        (fun c_eocc ->
           let c_occ = NO.(c_eocc.eo_occ) in
           let r = NO.(c_occ.so_ad.ca_r) in
           if r.symb.s_symb = r_n'.symb.s_symb then
             Some 
               (NO.mk_nocc r_n' r fv cond (fst info) st,
                mk_rand_occ r_n' c_eocc None cond fv (fst info) st)
               (* we also generate noccs, though we don't use them,
                  so that NameOccs prints them. not very pretty… *)
           else
             None)
        cs
    in

    List.split accs

  (* r' found in enc(m',r',k') *)
  | Fun (f, _, [Tuple [m'; Name _ as r'; Name (ksymb', _) as k']])
    when enc_f = f && ksymb'.s_symb = k.symb.s_symb ->
    let r_n' = Name.of_term r' in
    let k_n' = Name.of_term k' in

    (* if k' <> k we have a bad occ b/c of previous case *)
    (* look in m' also *)
    let occs ,accs = rec_call_on_subterms ~fv ~cond ~p ~info ~st m' in
    (* don't forget to also check in k', it could be an r *)
    (* actually maybe not but it doesn't hurt *)
    let occs2, accs2 =
      rec_call_on_subterms ~fv ~cond ~p ~info ~st k'
    in
    (* and add the occurrences for r' *)
    let l3 =
      List.filter_map
        (fun c_eocc ->
           let c_occ = NO.(c_eocc.eo_occ) in
           let r = NO.(c_occ.so_ad.ca_r) in
           if r.symb.s_symb = r_n'.symb.s_symb then
             Some 
               (NO.mk_nocc r_n' r fv cond (fst info) st,
                mk_rand_occ r_n' c_eocc (Some (m', k_n')) cond fv (fst info) st)
           else
             None)
        cs
    in
    let occs3, accs3 = List.split l3 in
    occs @ occs2 @ occs3, accs @ accs2 @ accs3
    
  | _ -> retry_on_subterms ()




(* constructs the formula expressing that a ciphertext occurrence
   c'=enc(m',r',k') is indeed in collision with c, and k' with k *)
let ciphertext_formula
    ~(negate : bool)
    (c':term)
    (c:term)
    (ca:ctxt_aux)
    : term =
  let {ca_m = m'; ca_r = r'; ca_k1 = k1; ca_kcoll = k} = ca in

  let () = (* sanity check *)
    match c' with
    | Fun (_f, _, [Tuple [m''; Name _ as r''; Name _ as k1']])
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

  else (* not used I think but still *)
    mk_or ~simpl:true
      (mk_not ~simpl:true (mk_eq ~simpl:true c c'))
      (mk_neqs ~simpl:true k.args k1.args)



                                          
(* constructs the formula expressing that an occurrence of a random r'
   is indeed a bad occurrence of the r from the ctxt_occ enc(m,r,k1):
   - if r' was found in enc(m',r',k'):
       phi_time(r) && k1 = k && r' = r && (k' <> k || m' <> m)
     or the negative phi_time(r) => k1 = k => r' = r => k' = k && m' = m
   - if r' was found directly:
       phi_time(r) && k1 = k && r' = r
     or the negative phi_time(r) => k1 = k => r' = r => false *)
(* note that it does not include the phi_time for r',
   as this is handled by NameOccs *)
(* similarly, no need to worry about the conditions or vars,
   as they were all added to the cond by mk_rand *)
let randomness_formula
    ~(negate : bool)
    (r':Name.t)
    (r:Name.t)
    ((eco, omk): (ectxt_occ * (term * Name.t) option))
      (* eco: occ where r was, omk = option (m',k') *)
  : term =
  let co = eco.eo_occ in
  let {ca_m=m; ca_r=rr; ca_k1=k1; ca_kcoll=k} = co.so_ad in
  assert (r = rr); (* sanity check *)
  let phi_time = (* phi_time(r) *)
    match co.so_occtype with
    | EI_direct -> mk_true
    | EI_indirect a -> NO.time_formula a eco.eo_source_ts
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




(*------------------------------------------------------------------*)
(** INT-CTXT tactic *)

(** parameters for the intctxt tactic *)
type intctxt_param = {
  ip_enc  : Symbols.fname;        (* encryption function *)
  ip_dec  : Symbols.fname;        (* decryption function *)
  ip_hash : Symbols.fname option; (* associated hash function *)
  ip_c    : term;                 (* ciphertext being decrypted *)
  ip_k    : Name.t;               (* key *)
  ip_t    : term option;          (* t when H is dec(c,k)=t *)
}

(** Finds the parameters of the integrity functions used in the hypothesis,
    if any *)
let intctxt_param
    ~(hyp_loc : L.t)
    (contx : Constr.trace_cntxt)
    (hyp : term)
    (s : TS.sequent)
  : intctxt_param
  =
  let fail () =
    soft_failure ~loc:hyp_loc
      (Tactics.Failure "can only be applied on an hypothesis of the form \
dec(c,k) <> fail or dec(c,k) = t (or the symmetric equalities)")
  in
  let info = NO.EI_direct, contx in
  let table = contx.table in

  (* try to write t as dec(c,k) *)
  let try_t (t:term) : intctxt_param option =
    let t = NO.expand_macro_check_all info t in
    match t with
    | Fun (dec, _, [Tuple [m; tk]]) ->
      begin
        match NO.expand_macro_check_all info tk with
        | Name _ as k when Symbols.is_ftype dec Symbols.SDec table ->
          begin
            match Symbols.Function.get_data dec table with
            | Symbols.AssociatedFunctions [enc] ->
              Some {ip_enc=enc; ip_dec=dec; ip_hash=None;
                    ip_c=m; ip_k= Name.of_term k; ip_t=None}

            | Symbols.AssociatedFunctions [enc; h] ->
              Some {ip_enc=enc; ip_dec=dec; ip_hash=Some h;
                    ip_c=m; ip_k=Name.of_term k; ip_t=None}
            | _ -> assert false (* sanity check *)
          end
        | _ -> None
      end
    | _ -> None
  in

  (* try to write hyp as u <> v *)
  match destr_neq hyp with (* todo use reduce *)
  | Some (u, v) when u = mk_fail -> (* fail <> v: write v as dec(c,k) *)
    (match try_t v with | Some p -> p | None -> fail ())
  | Some (u, v) when v = mk_fail -> (* u <> fail: write u as dec(c,k) *)
    (match try_t u with | Some p -> p | None -> fail ())
  | Some _ -> fail () (* u <> v but neither u nor v is fail *)
  | None ->  (* not a disequality - check if equality *)
    match TS.Reduce.destr_eq s Equiv.Local_t hyp with
    | None -> fail () (* not an equality *)
    | Some (u,v) ->
      match try_t u, try_t v with
      | Some p, _ -> (* dec(c,k) = v *)
        {p with ip_t = Some v}
      | _, Some p ->
        {p with ip_t = Some u} (* u = dec(c,k) *)
      | _, _ -> fail ()




let intctxt
    (h : lsymb)
    (s : sequent)
  : sequent list
  =
  (* find parameters *)
  let _, hyp = Hyps.by_name h s in
  let contx = TS.mk_trace_cntxt s in
  let env = (TS.env s).vars in
  
  let {ip_enc=enc_f; ip_dec=dec_f; ip_hash=hash_f;
       ip_c=c; ip_k=k; ip_t=t} = 
    intctxt_param ~hyp_loc:(L.loc h) contx hyp s
  in
      
  
  let pp_k ppf () = Fmt.pf ppf "%a" Name.pp k in
  let pp_rand ppf () = Fmt.pf ppf "randomness" in

  Printer.pr "@[<v 0>";
  (* get the key bad occs and the ciphertext occs *)
  let get_bad:((term, ctxt_aux) NO.f_fold_occs) =
    get_bad_occs_and_ciphertexts k c enc_f dec_f ~hash_f
  in
  let phis_bad_k, phis_ctxt, _, ctxt_occs =
    NO.occurrence_formulas_with_occs ~pp_ns:(Some pp_k)
      ciphertext_formula
      get_bad contx env [c]
  in

  Printer.pr "@;@;";
  (* get the bad randomness occurrences *)
  let get_bad: (Name.t, ectxt_occ * ((term * Name.t) option)) NO.f_fold_occs =
    get_bad_randoms k ctxt_occs enc_f
  in
  let _, phis_bad_r =
    NO.occurrence_formulas ~pp_ns:(Some pp_rand)
      randomness_formula
      get_bad contx env [c]
  in

  let phi_t = match t with
    | None -> []
    | Some t -> [mk_eq ~simpl:true t mk_fail]
  in

  (* remove trivial formulas. *)
  let nbr = List.length phis_bad_r in
  let filter_tf = List.filter ((<>) mk_false) in
  let phis_bad_r = filter_tf phis_bad_r in
  let nbr' = List.length phis_bad_r in
(* only for bad random occurrences, since 1) we generate a lot of false
     bad occs (of a ciphertext with itself), and 2) for key or ciphertexts
     it would be confusing *)

  if nbr > nbr' then
    Printer.pr "       among which %d trivial randomness occurrence%signored@;"
      (nbr-nbr')
      (if nbr - nbr' = 1 then " is " else "s are ");

  let nbc = List.length phis_ctxt in
  Printer.pr "@;%d possible ciphertext%s found.@;@]"
    nbc (if nbc = 1 then "" else "s");

  
  let phis = phi_t @ phis_bad_k @ phis_bad_r @ phis_ctxt in

  let g = TS.goal s in 
  let ciphertext_goals =
    List.map
    (fun phi -> TS.set_goal (mk_impl ~simpl:false phi g) s)
    phis
  in


    (* copied from old euf, handles the composition goals *)
  let tag_s =
    let f =
      Prover.get_oracle_tag_formula (Symbols.to_string enc_f)
    in
    (* if the hash is not tagged, the formula is False, and we don't create
       another goal. *)
    if f = Term.mk_false
    then []
    else
      (* else, we create a goal where m,sk satisfy the axiom *)
      let uvarm, uvarkey,f = match f with
        | Quant (ForAll,[uvarm;uvarkey],f) -> uvarm,uvarkey,f
        | _ -> assert false
      in

      match Vars.ty uvarm,Vars.ty uvarkey with
      | Type.(Message, Message) -> let f = Term.subst [
          ESubst (Term.mk_var uvarm,c);
          ESubst (Term.mk_var uvarkey, Name.to_term k);] f in
        [TS.set_goal
           (Term.mk_impl f (TS.goal s)) s]

      | _ -> assert false 
  in

  tag_s @ ciphertext_goals

  

(*------------------------------------------------------------------*)
let intctxt_tac args s =
  let hyp = match args with
    | [hyp] -> hyp
    | _ -> 
      hard_failure
        (Failure "euf requires one argument: hypothesis")
  in
  match TraceLT.convert_args s [hyp] (Args.Sort Args.String) with
  | Args.Arg (Args.String hyp) -> wrap_fail (intctxt hyp) s
  | _ -> bad_args ()

(*------------------------------------------------------------------*)
let () =
  T.register_general "intctxt"
    ~tactic_help:{
      general_help =
        "Apply the INT-CTXT axiom to the given hypothesis name.";          
      detailed_help =
        "applies to a hypothesis of the form dec(c,k)<>fail, \
or dec(c,k) = t (in the latter case, generates as an additional goal \
that t <> fail)";
      usages_sorts = [];
      tactic_group = Cryptographic }
    ~pq_sound:true
    (LowTactics.gentac_of_ttac_arg intctxt_tac)

