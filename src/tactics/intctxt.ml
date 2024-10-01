(* INT-CTXT trace tactic *)
open Squirrelcore
open Term
open Utils
open Ppenv

module Args = TacticsArgs
module L = Location
module SE = SystemExpr
module TS = TraceSequent
module LT = LowTactics


type sequent = TS.sequent

type lsymb = Typing.lsymb

module O = Occurrences
module RO = RandomnessOccurrences
module Name = O.Name
type name = Name.t 


(*------------------------------------------------------------------*)
let wrap_fail = LT.TraceLT.wrap_fail
let soft_failure = Tactics.soft_failure
let hard_failure = Tactics.hard_failure


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
    - as enc key
    - as dec key (normally not present for int-ctxt, but admissible)
    - hashed under any key, if an associated hash function is declared
      (this is not standard, and only used for Charlie's weird assumption)

    2) occurrences of ciphertexts, with a key that has
    the same symbol as [k]. Store as collision in these occurrences the
    [ciphertext], which is the term we were trying to decrypt. *)
let get_bad_occs
    (env : Env.t)
    ~(k : name)
    ~(ciphertext : term)
    ~(enc_f : Symbols.fname) (* encryption function *)
    ~(dec_f : Symbols.fname) (* decryption function *)
    ?(hash_f : Symbols.fname option=None) (* associated hash function. *)
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

  (* non ptime deterministic variable -> forbidden *)
  (* (this is where we used to check variables
     were only timestamps or indices) *)
  | Var v ->
    soft_failure
      (Tactics.Failure
         (Fmt.str "terms contain a non-ptime variable: %a" Vars.pp v))

  (* a name with the same symbol as the key *)
  | Name (ns, nargs) as n when ns.s_symb = k.symb.s_symb ->
    let n = Name.of_term n in
    (* generate an occurrence, and recurse on nargs *)
    let occs = List.concat_map (rec_call info) nargs in
    let occ =
      mk_simple_occ
        ~content:(BadName n)
        ~collision:(BadName k)
        ~data:NoData
        ~vars:info.pi_vars
        ~cond:info.pi_cond
        ~typ:info.pi_occtype
        ~sub:info.pi_subterm
        ~show:Show
    in
    occ :: occs


  (* encryption w/ a name that could be the right key *)
  (* an actual random must be used as random *)
  (* we record this ciphertext occurrence, but allow the key *)
  | App (Fun (f, _), [Tuple [m; Name _ as r; Name (ksb', kargs') as k']])
    when f = enc_f && k.symb.s_symb = ksb'.s_symb ->
    (* look in m, r', kargs' *)
    let occs = List.concat_map (rec_call info) (m :: r :: kargs') in
    (* and record the ciphertext *)
    let oc = mk_simple_occ
        ~content:(Ciphertext t)
        ~collision:(Ciphertext ciphertext)
        ~data: 
          (DataCiphertext {msg=m; 
                           rand=Name.of_term r; 
                           key=Name.of_term k'; 
                           keycoll=k})
        ~vars:info.pi_vars 
        ~cond:info.pi_cond 
        ~typ:info.pi_occtype 
        ~sub:info.pi_subterm
        ~show:Hide (* we don't want to print these *)
    in
    oc :: occs

  (* decryption w/ a name that could be the right key *)
  (* for int-ctxt: normally decryption is not allowed, there is only
     an oracle to check dec ≠ fail, but since when dec ≠ fail the attacker
     can compute the decryption himself, allowing a full dec oracle
     is the same *)
  | App (Fun (f, _), [Tuple [c; Name (ksb', kargs')]])
    when f = dec_f && k.symb.s_symb = ksb'.s_symb ->
    (* still look in c, kargs' *)
    List.concat_map (rec_call info) (c :: kargs')

  (* hash oracle: when enc has an associated hash function,
     we discard bad occurrences of k under any hash with any key
     (in the hashed message, not in the hashing key)
     we do keep the ciphertexts though *)
  | App (Fun (f, _), [Tuple [m; Name _ as k']])
    when hash_f = Some f ->
    (* look in m and k' (k is not a hash key, it should not be used as k') *)
    let occs1 = rec_call info m in
    let occs2 = rec_call info k' in        
    (* discard bad key occurrences in m *)
    let occs1 =
      List.filter (fun o -> match o.EOS.EO.SO.so_cnt with
          | BadName _ -> false
          | _ -> true)
        occs1
    in
    occs1@occs2

  | _ -> retry ()



(*------------------------------------------------------------------*)
(** {2 INT-CTXT parameters} *)
(** Utilities to find the parameters (which encryption symbol, which
    challenge ciphertext, etc.) when applying int-ctxt *)

(** parameters for the intctxt tactic *)
type intctxt_param = {
  ip_enc  : Symbols.fname;        (* encryption function *)
  ip_dec  : Symbols.fname;        (* decryption function *)
  ip_hash : Symbols.fname option; (* associated hash function *)
  ip_c    : term;                 (* ciphertext being decrypted *)
  ip_k    : name;                 (* key *)
  ip_t    : term option;          (* t when H is dec(c,k) = t *)
}

(** Finds the parameters of the integrity functions used in the hypothesis *)
let intctxt_param
    ~(loc : L.t)
    (hyp : term) (* the hypothesis where we want to apply int-ctxt *)
    (s : TS.sequent)
  : intctxt_param
  =
  let table = TS.table s in

  let contx = TS.mk_trace_cntxt s in
  let info = O.EI_direct, contx in

  let exception NotDec in

  (* try to write t as dec(c,k) *)
  let try_t (t:term) : intctxt_param =
    let t = O.expand_macro_check_all info t in
    match t with
    | App (Fun (dec, _), [Tuple [m; tk]]) ->
      begin
        match O.expand_macro_check_all info tk with
        | Name _ as k when
            Symbols.OpData.(is_abstract_with_ftype dec SDec table) ->
          begin
            match Symbols.OpData.get_abstract_data dec table with
            | _, [enc] ->
              {ip_enc=enc; ip_dec=dec; ip_hash=None;
               ip_c=m; ip_k= Name.of_term k; ip_t=None}

            | _, [enc; h] ->
              {ip_enc=enc; ip_dec=dec; ip_hash=Some h;
               ip_c=m; ip_k=Name.of_term k; ip_t=None}
            | _ -> assert false (* sanity check *)
          end
        | _ -> raise NotDec
      end
    | _ -> raise NotDec
  in

  (* try to write hyp as u <> v *)
  try
    match Term.destr_neq hyp with (* TODO use reduce *)
    | Some (u, v) when Term.equal u mk_fail -> (* fail <> v:
                                                  write v as dec(c,k) *)
      try_t v
    | Some (u, v) when Term.equal v mk_fail -> (* u <> fail:
                                                  write u as dec(c,k) *)
      try_t u
    | Some _ -> raise NotDec (* u <> v but neither u nor v is fail *)
    | None ->  (* not a disequality - check if equality *)
      match TS.Reduce.destr_eq s Equiv.Local_t hyp with
      | None -> raise NotDec (* not an equality *)
      | Some (u,v) ->
        try
          let p = try_t u in (* dec(c,k) = v *)
          {p with ip_t = Some v}
        with
        | NotDec ->
          let p = try_t v in (* u = dec(c,k) *)
          {p with ip_t = Some u}
  with
  | NotDec ->
    soft_failure ~loc
      (Tactics.Failure 
         "can only be applied on an hypothesis of the form \
          dec(c,k) <> fail or dec(c,k) = t (or the symmetric equalities)")



(*------------------------------------------------------------------*)
(** The INT-CTXT tactic *)
let intctxt
    ?(use_path_cond : bool = false)
    (h : lsymb)
    (s : sequent)
  : sequent list
  =
  let ppe = default_ppe ~table:(TS.table s) () in
  let loc = L.loc h in

  (* Find parameters *)
  let _, hyp = TS.Hyps.by_name_k h Hyp s in
  let hyp = LT.as_local ~loc hyp in (* FIXME: allow global hyps? *)
  let contx = TS.mk_trace_cntxt s in
  let env = TS.env s in
  let hyps = TS.get_trace_hyps s in

  let icp = intctxt_param ~loc hyp s in

  (* Printers for [k] and the randomness *)
  let pp_k ppf () = Fmt.pf ppf "%a" (Name.pp ppe) icp.ip_k in
  let pp_rand ppf () = Fmt.pf ppf "randomness" in

  (* Find bad occurrences of [k], and all ciphertexts with [k] *)
  let get_bad_kc : EOS.f_fold_occs =
    get_bad_occs env ~k:icp.ip_k ~ciphertext:icp.ip_c
      ~enc_f:icp.ip_enc ~dec_f:icp.ip_dec ~hash_f:icp.ip_hash
  in

  let occs_kc =
    EOS.find_all_occurrences ~mode:Iter.PTimeNoSI ~pp_descr:(Some pp_k)
      get_bad_kc
      hyps contx env
      (icp.ip_c :: icp.ip_k.args)
  in

  (* Split occurrences of [k] from the ciphertexts *)
  let occs_k, occs_c =
    List.fold_left 
      (fun (occs_k, occs_c) (occ:EOS.ext_occ) ->
         match occ.eo_occ.so_cnt with 
         | BadName _ -> occ::occs_k, occs_c
         | Ciphertext _ -> occs_k, occ::occs_c
         | _ -> assert false)
      ([],[])
      occs_kc
  in

  (* Put them back in order. idk if that's really useful, it was just
     to keep the historical order *) 
  let occs_k, occs_c = List.rev occs_k, List.rev occs_c in

  (* We can now generate the formulas for all the bad key occs. 
     We do not generate formulas for the ciphertexts occs: these are only used
     to check the randomness conditions afterwards. *)
  let phis_k =
    List.map (EOF.occurrence_formula ~negate:false ~use_path_cond) occs_k
  in

  (* We also generate the formulas for each ciphertext found.
     (we do that separately just so they don't get mixed with the bad occs) *)
  let phis_c =
    List.map (EOF.occurrence_formula ~negate:false ~use_path_cond) occs_c
  in

  (* We now search for bad use of all randoms used in occs_c *)
  let get_bad_randoms : ROS.f_fold_occs =
    RO.get_bad_randoms env ~k:icp.ip_k ~enc_f:icp.ip_enc ~ciphertexts:occs_c
  in

  let occs_r =
    ROS.find_all_occurrences ~mode:Iter.PTimeNoSI ~pp_descr:(Some pp_rand)
      get_bad_randoms
      hyps contx env
      [icp.ip_c; Name.to_term icp.ip_k]
  in

  let phis_r =
    List.map (ROF.occurrence_formula ~negate:false ~use_path_cond) occs_r
  in

  (* Finally, in case the term [t] equal to the decryption was not [fail],
     we generate an additional formula stating that it is equal to [fail] *)
  let phi_t = match icp.ip_t with
    | None -> []
    | Some t -> [Term.mk_eq ~simpl:true t mk_fail]
  in

  (* remove trivial formulas. *)
  let nbr = List.length phis_r in
  let filter_tf = List.filter ((<>) mk_false) in
  let phis_r = filter_tf phis_r in
  let nbr' = List.length phis_r in
  (* only for bad random occurrences, since 1) we generate a lot of false
     bad occs (of a ciphertext with itself), and 2) for key or ciphertexts
     it would be confusing *)

  if nbr > nbr' then
    Printer.pr "       among which %d trivial randomness occurrence%signored@;"
      (nbr-nbr')
      (if nbr - nbr' = 1 then " is " else "s are ");

  let nbc = List.length phis_c in
  Printer.pr "@;%d possible ciphertext%s found.@;@]"
    nbc (if nbc = 1 then "" else "s");


  let phis = phi_t @ phis_k @ phis_r @ phis_c in

  let g = TS.conclusion s in 
  let ciphertext_goals =
    List.map
      (fun phi -> TS.set_conclusion (mk_impl ~simpl:false phi g) s)
      phis
  in


  (* copied from old euf, handles the composition goals *)
  let tag_s =
    match Oracle.get_oracle icp.ip_enc (TS.table s) with
    (* if the hash is not tagged, we don't create another goal. *)
    | None -> []
    | Some f ->
      (* else, we create a goal where m,sk satisfy the axiom *)
      let uvarm, uvarkey,f = match f with
        | Quant (ForAll,[uvarm;uvarkey],f) -> uvarm,uvarkey,f
        | _ -> assert false
      in

      match Vars.ty uvarm,Vars.ty uvarkey with
      | Type.(Message, Message) -> let f = Term.subst [
          ESubst (Term.mk_var uvarm, icp.ip_c);
          ESubst (Term.mk_var uvarkey, Name.to_term icp.ip_k);] f in
        [TS.set_conclusion
           (Term.mk_impl f (TS.conclusion s)) s]

      | _ -> assert false 
  in

  tag_s @ ciphertext_goals



(*------------------------------------------------------------------*)
let intctxt_tac args s =
  let hyp = match args with
    | [hyp] -> hyp
    | _ -> 
      hard_failure
        (Failure "intctxt requires one argument: hypothesis")
  in
  match LT.TraceLT.convert_args s [hyp] (Args.Sort Args.String) with
  | Args.Arg (Args.String hyp) -> wrap_fail (intctxt hyp) s

  | _ -> LT.bad_args ()

(*------------------------------------------------------------------*)
let () =
  LT.T.register_general "intctxt"
    ~pq_sound:true
    (LowTactics.gentac_of_ttac_arg intctxt_tac)
