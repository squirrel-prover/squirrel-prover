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



(*------------------------------------------------------------------*)
(** The INT-CTXT tactic *)
let intctxt
    ?use_path_cond
    (h : lsymb)
    (s : sequent)
  : sequent list
  =
  (* find parameters *)
  let _, hyp = Hyps.by_name h s in
  let contx = TS.mk_trace_cntxt s in
  let env = TS.env s in

  let {ip_enc=enc_f; ip_dec=dec_f; ip_hash=hash_f;
       ip_c=c; ip_k=k; ip_t=t} = 
    intctxt_param ~hyp_loc:(L.loc h) contx hyp s
  in
  
  let pp_k ppf () = Fmt.pf ppf "%a" Name.pp k in
  let pp_rand ppf () = Fmt.pf ppf "randomness" in

  Printer.pr "@[<v 0>";
  (* get the key bad occs and the ciphertext occs *)
  let get_bad:((term, EncRandom.ctxt_aux) NO.f_fold_occs) =
    EncRandom.get_bad_occs_and_ciphertexts
      env k [] c enc_f dec_f ~hash_f ~pk_f:None
      ~dec_allowed:EncRandom.Allowed
  in
  let phis_bad_k, phis_ctxt, _, ctxt_occs =
    NO.occurrence_formulas_with_occs ~mode:PTimeNoSI ~pp_ns:(Some pp_k)
      EncRandom.ciphertext_formula
      get_bad contx env (c :: k.Name.args)
  in

  (* get the bad randomness occurrences *)
  let get_bad: (Name.t, EncRandom.ectxt_occ * ((term * Name.t) option)) NO.f_fold_occs =
    EncRandom.get_bad_randoms env k ctxt_occs enc_f
  in
  let _, phis_bad_r =
    (* FEATURE: allow the user to set [use_path_cond] to true *)
    NO.occurrence_formulas ~mode:PTimeNoSI ?use_path_cond ~pp_ns:(Some pp_rand)
      (EncRandom.randomness_formula ?use_path_cond)
      get_bad contx env (c :: k.Name.args)
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
      (* XXX depends on Prover_state *)
      ProverLib.get_oracle_tag_formula (Symbols.to_string enc_f)
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
        (Failure "intctxt requires one argument: hypothesis")
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

