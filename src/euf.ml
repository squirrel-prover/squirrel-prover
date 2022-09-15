(* EUF trace tactic *)
open Term
open Utils

module Args = TacticsArgs
module L = Location
module SE = SystemExpr
module NO = NameOccs

module TS = TraceSequent

module Hyps = TS.LocalHyps

type sequent = TS.sequent

type lsymb = Theory.lsymb

module MP = Match.Pos
module Sp = MP.Sp

open LowTactics

(*------------------------------------------------------------------*)
let wrap_fail = TraceLT.wrap_fail
let soft_failure = Tactics.soft_failure
let hard_failure = Tactics.hard_failure

(* integrity occurrence *)
type int_occ = ((term * nsymb), unit) NO.simple_occ
type int_occs = int_occ list

let mk_int_occ
    (t:term) (tcoll:term) (k:nsymb) (kcoll:nsymb)
    (cond:terms) (v:Vars.vars) (st:term) : int_occ =
  NO.mk_simple_occ (t,k) (tcoll,kcoll) () v cond st


(*------------------------------------------------------------------*)
(* Look for occurrences using NameOccs *)

(**  *)
let get_bad_occs
    (m:term)
    (k:nsymb)
    (int_f:fsymb) (* function with integrity (hash, signature) *)
    ?(pk_f:fsymb option=None) (* public key function. Must be None iff hash *)
    (retry_on_subterms : (unit -> NO.n_occs * int_occs))
    (rec_call_on_subterms :
       (fv:Vars.vars ->
        cond:terms ->
        p:MP.pos ->
        info:NO.expand_info ->
        st:term ->
        term ->
        NO.n_occs * int_occs))
    ~(info:NO.expand_info)
    ~(fv:Vars.vars)
    ~(cond:terms)
    ~(p:MP.pos)
    ~(st:term)
    (t:term) 
  : NO.n_occs * int_occs =
  (* handles a few cases, using rec_call_on_subterm for rec calls, and calls retry_on_subterm for the rest *)
  match t with
  | Var v when not (Type.is_finite (Vars.ty v)) ->
    soft_failure
      (Tactics.Failure "can only be applied on ground terms")

  | Name k' when k'.s_symb = k.s_symb ->
    [NO.mk_nocc k' k fv cond st],
    []

  | Fun (f, _, [tk']) when pk_f = Some f -> (* public key *)
    begin
      match NO.expand_macro_check_all info tk' with
      | Name _ -> [], [] (* pk(k'): no occ, even if k'=k *)
      | _ -> retry_on_subterms () (* otherwise look in tk' *)
    end
    
  (* hash verification oracle: test u = h(m', k). Search recursively in u, m', but do not record
     m' as a hash occurrence. *)
  | Fun (f, _, [u; Fun (g, _, [Tuple [m'; Name k']])])
    when f = f_eq && g = int_f && pk_f = None && k'.s_symb = k.s_symb ->
    let (occs1, accs1) = rec_call_on_subterms ~fv ~cond ~p ~info ~st:t u in
    let (occs2, accs2) = rec_call_on_subterms ~fv ~cond ~p ~info ~st:t m' in
    occs1 @ occs2, accs1 @ accs2

  (* hash verification oracle (symmetric case). can we avoid duplication? *)
  | Fun (f, _, [Fun (g, _, [Tuple [m'; Name k']]); u])
    when f = f_eq && g = int_f && pk_f = None && k'.s_symb = k.s_symb ->
    let (occs1, accs1) = rec_call_on_subterms ~fv ~cond ~p ~info ~st:t u in
    let (occs2, accs2) = rec_call_on_subterms ~fv ~cond ~p ~info ~st:t m' in
    occs1 @ occs2, accs1 @ accs2

  | Fun (f, _, [Tuple [m'; tk']]) when f = int_f ->
    begin
      match NO.expand_macro_check_all info tk' with
      (* hash/sign/etc w/ a name that could be the right key *) 
      (* record this hash occurrence, but allow the key *)
      (* todo: actually why don't we always do this, even if it's the wrong key? *)
      | Name k' when k.s_symb = k'.s_symb  ->
        let occs, acc = rec_call_on_subterms ~fv ~cond ~p ~info ~st m' in 
        occs,
        acc @ [mk_int_occ m' m k' k  cond fv st]

      (* if we can't be sure it could be the key *)
      (* don't record the hash occ, but look for bad occurrences in m and tk *)
      (* (worst case, it was actually the key, and we'll miss the assumption that 
         the message could be m in the goal for the key's occurrence) *)
      (* IS THAT ACTUALLY SOUND?? *)
      | _ -> retry_on_subterms ()
    end

  | _ -> retry_on_subterms ()


(* converts the contents of an int_occ to a term, for inclusion tests *)
let integrity_converter : ((term * nsymb), unit) NO.converter =
  { conv_cnt = (fun (t, n) -> mk_eq ~simpl:false (mk_tuple [t; mk_name n]) mk_zero);
    conv_ad = (fun () -> mk_false) }

(* constructs the formula expressing that an integrity occurrence m',k' is indeed in collision with m, k *)
let integrity_formula
    ~(negate : bool)
    ((m', k') : term * nsymb)
    ((m, k) : term * nsymb)
    ()
    : term =
  assert (k.s_symb = k'.s_symb); (* every occurrence we generated should satisfy this *)
  if not negate then 
    mk_and ~simpl:true
      (mk_eq ~simpl:true m m')
      (mk_indices_eq ~simpl:true k.s_indices k'.s_indices)
  else
    mk_or ~simpl:true
      (mk_not ~simpl:true (mk_eq ~simpl:true m m'))
      (mk_indices_neq ~simpl:true k.s_indices k'.s_indices)




(*------------------------------------------------------------------*)
(* EUF tactic *)

(* parameters for the integrity occurrence: key, signed or hashed message,
   signature checked or compared w/ the hash, sign/hash function, pk function if any *) 
type euf_param = {ep_key:nsymb;
                  ep_intmsg:term;
                  ep_term:term;
                  ep_int_f:fsymb;
                  ep_pk_f:fsymb option;}


(** Finds the parameters of the integrity functions used in the hypothesis, if any *)
let euf_param
    ~(hyp_loc : L.t)
    (contx : Constr.trace_cntxt)
    (hyp : term)
    (s : TS.sequent)
  : euf_param
  =
  let fail () =
    soft_failure ~loc:hyp_loc
      (Tactics.Failure "can only be applied on an hypothesis of the form checksign(m, s, pk(k)), hash(m, k) = t, or the symmetric equality")
  in
  let info = NO.EI_direct, contx in
  let table = contx.table in

  (* try to write hyp as u = v *)
  match TS.Reduce.destr_eq s Equiv.Local_t hyp with
  | Some (u, v) -> (* an equality: try to see u or v as h(m, k) *)
    let u = NO.expand_macro_check_all info u in
    let v = NO.expand_macro_check_all info v in
    let try_t (t:term) (t':term) : euf_param option =
      match t with
      | Fun (f, _, [Tuple [m; tk]]) ->
        begin
          match NO.expand_macro_check_all info tk with
          | Name k when Symbols.is_ftype f Symbols.Hash table ->
            Some {ep_key=k; ep_intmsg=m; ep_term=t'; ep_int_f=f; ep_pk_f=None}
          | _ -> None
        end
      | _ -> None
    in
    begin
      match try_t u v with
      | Some p -> p
      | None ->
        match try_t v u with
        | Some p -> p
        | None -> fail ()
    end
  | None -> (* not an equality: try to see if it's checksign(m,s,pk) *)
    match NO.expand_macro_check_all info hyp with
    | Fun (f, _, [Tuple [m; s; tpk]]) ->
      begin
        match NO.expand_macro_check_all info tpk with
        | Fun (g, _, [tk]) ->
          begin
            match Theory.check_signature table f g, NO.expand_macro_check_all info tk with
            | Some sg, Name k ->
              {ep_key=k; ep_intmsg=m; ep_term=s; ep_int_f=sg; ep_pk_f=Some g}
            | _ -> fail ()
          end
        | _ -> fail ()
      end
    | _ -> fail ()
                   


let euf
    (h : lsymb)
    (s : sequent)
  : sequent list
  =
  (* find parameters *)
  let id, hyp = Hyps.by_name h s in
  let contx = TS.mk_trace_cntxt s in
  let env = (TS.env s).vars in
  
  let {ep_key=k; ep_intmsg=m; ep_term=t; ep_int_f=int_f; ep_pk_f=pk_f} =
    euf_param ~hyp_loc:(L.loc h) contx hyp s
  in
      
  
  let pp_k ppf () = Fmt.pf ppf "%a" Term.pp_nsymb k in

  (* apply euf *)
  let get_bad:((term*nsymb, unit) NO.f_fold_occs) = get_bad_occs m k int_f ~pk_f in
  let phis_bad, phis_int =
    NO.occurrence_formulas ~pp_ns:(Some pp_k)
      integrity_converter integrity_formula
      get_bad contx env [t; m]
  in

  (* todo remove duplicates in occs *)
  let phis = phis_bad @ phis_int in

  let g = TS.goal s in 
  let integrity_goals =
    List.map
    (fun phi -> TS.set_goal (mk_impl ~simpl:false phi g) s)
    phis
  in
  
  (* copied from old euf, handles the composition goals *)
  let tag_s =
    let f =
      Prover.get_oracle_tag_formula (Symbols.to_string int_f)
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
          ESubst (Term.mk_var uvarm,m);
          ESubst (Term.mk_var uvarkey,Term.mk_name k);] f in
        [TS.set_goal
           (Term.mk_impl f (TS.goal s)) s]

      | _ -> assert false 
  in
  
  tag_s @ integrity_goals


  

(*------------------------------------------------------------------*)
let euf_tac args s =
  let hyp = match args with
    | [hyp] -> hyp
    | _ -> 
      hard_failure
        (Failure "euf requires one argument: hypothesis")
  in
  match TraceLT.convert_args s [hyp] (Args.Sort Args.String) with
  | Args.Arg (Args.String hyp) -> wrap_fail (euf hyp) s
  | _ -> bad_args ()

(*------------------------------------------------------------------*)
let () =
  T.register_general "euf"
    ~tactic_help:{
      general_help =
        "Apply the euf axiom to the given hypothesis name.";          
      detailed_help =
        "If the hash has been declared with a tag formula, applies \
         the tagged version.  given tag. Tagged eufcma, with a tag T, \
         says that, under the syntactic side condition, a hashed \
         message either satisfies the tag T, or was honestly \
         produced. The tag T must refer to a previously defined axiom \
         f(mess,sk), of the form forall (m:message,sk:message).";
      usages_sorts = [];
      tactic_group = Cryptographic }
    ~pq_sound:true
    (LowTactics.gentac_of_ttac_arg euf_tac)

