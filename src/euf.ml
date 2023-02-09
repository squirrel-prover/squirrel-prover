(* EUF trace tactic *)
open Term
open Utils

module Args = TacticsArgs
module L = Location
module SE = SystemExpr
module NO = NameOccs
module Name = NO.Name
                
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
type int_occ = ((term * Name.t), unit) NO.simple_occ
type int_occs = int_occ list

let mk_int_occ
    (t:term) (tcoll:term) (k:Name.t) (kcoll:Name.t)
    (cond:terms) (fv:Vars.vars) (ot:NO.occ_type) (st:term) : int_occ =
  let fv, sigma = Term.refresh_vars fv in
  let cond = List.map (Term.subst sigma) cond in
  let ot = NO.subst_occtype sigma ot in
  let t = Term.subst sigma t in
  let k = Name.subst sigma k in
  let st = subst sigma st in
  NO.mk_simple_occ (t,k) (tcoll,kcoll) () fv cond ot st


(*------------------------------------------------------------------*)
(* Look for occurrences using NameOccs *)

(**  *)
let get_bad_occs
    (env : Env.t)
    (m:term)
    (k:Name.t)
    (int_f:Symbols.fname) (* function with integrity (hash, signature) *)
    ?(pk_f:Symbols.fname option=None) (* public key function.
                                         Must be None iff hash *)
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
  (* handles a few cases, using rec_call_on_subterm for rec calls,
     and calls retry_on_subterm for the rest *)
  (* only use this rec_call shorthand if the parameters don't change! *)
  let rec_call ?(st = st) = (* rec call on a list *)
    List.flattensplitmap (rec_call_on_subterms ~fv ~cond ~p ~info ~st)
  in

  (* variables quantified above the current point are considered deterministic,
     so we add them to the env usd for "is_ptime_deducible" *)
  let env =
    Env.update ~vars:(Vars.add_vars (Vars.Tag.global_vars ~const:true fv) env.vars) env
  in
  match t with
  | _ when HighTerm.is_ptime_deducible ~const:`Exact ~si:false env t -> ([], [])
  (* SI not needed here *)

  (* non ptime deterministic variable -> forbidden *)
  (* (this is where we used to check variables were only timestamps or indices) *)
  | Var v ->
    soft_failure
      (Tactics.Failure (Fmt.str "terms contain a non-ptime variable: %a" Vars.pp v))

  (* occurrence of the signing/hash key *)
  | Name (ksb', kargs') as k' when ksb'.s_symb = k.symb.s_symb ->
    (* generate an occ, and also recurse on kargs' *)
    let occs1, accs1 = rec_call kargs' in
    (NO.mk_nocc (Name.of_term k') k fv cond (fst info) st) :: occs1,
    accs1

  (* occurrence of the public key (for the signature case only) *)
  | Fun (f, _, [tk']) when pk_f = Some f -> (* public key *)
    begin
      match NO.expand_macro_check_all info tk' with
      | Name (_, tkargs') -> rec_call tkargs'
      (* pk(k'): no occ,
         even if k'=k, just look in k' args *)
      | _ -> retry_on_subterms () (* otherwise look in tk' *)
    end
    

  (* hash verification oracle: test u = h(m', k).
     Search recursively in u, m', kargs', but do not record
     m' as a hash occurrence. *)
  | Fun (f, _, [u; Fun (g, _, [Tuple [m'; Name (ksb', kargs')]])])
    when f = f_eq && g = int_f && pk_f = None && ksb'.s_symb = k.symb.s_symb ->
    rec_call ~st:t (u :: m' :: kargs') (* change st *)


  (* hash verification oracle (converse case h(m', k) = u). *)
  | Fun (f, _, [Fun (g, _, [Tuple [m'; Name (ksb', kargs')]]); u])
    when f = f_eq && g = int_f && pk_f = None && ksb'.s_symb = k.symb.s_symb ->
    rec_call ~st:t (u :: m' :: kargs') (* change st *)

  (* hash/sign/etc w/ a name that could be the right key *) 
  (* record this hash occurrence, but allow the key *)
  (* q: actually why don't we always do this,
               even if it's the wrong key?
     a: that would be sound but generate too many occs *)
  | Fun (f, _, [Tuple [m'; Name (ksb', kargs') as k']])
    when f = int_f && k.symb.s_symb = ksb'.s_symb ->
    let occs, accs = rec_call (m' :: kargs') in
    occs,
    accs @ [mk_int_occ m' m (Name.of_term k') k cond fv (fst info) st]
             
  | _ -> retry_on_subterms ()


(* constructs the formula expressing that an integrity occurrence m',k'
   is indeed in collision with m, k *)
let integrity_formula
    ~(negate : bool)
    ((m', k') : term * Name.t)
    ((m, k) : term * Name.t)
    ()
    : term =
  (* every occurrence we generated should satisfy this *)
  assert (k.symb.s_symb = k'.symb.s_symb); 

  if not negate then 
    mk_and ~simpl:true
      (mk_eq ~simpl:true m m')
      (mk_eqs ~simpl:true k.args k'.args)
  else
    mk_or ~simpl:true
      (mk_not ~simpl:true (mk_eq ~simpl:true m m'))
      (mk_neqs ~simpl:true k.args k'.args)

(*------------------------------------------------------------------*)
(** {2 EUF tactic} *)

(* parameters for the integrity occurrence: key, signed or hashed message,
   signature checked or compared w/ the hash, sign/hash function,
   pk function if any *) 
type euf_param = {ep_key:Name.t;
                  ep_intmsg:term;
                  ep_term:term;
                  ep_int_f:Symbols.fname;
                  ep_pk_f:Symbols.fname option;}


(** Finds the parameters of the integrity functions used in the hypothesis,
    if any *)
let euf_param
    ~(hyp_loc : L.t)
    (contx : Constr.trace_cntxt)
    (hyp : term)
    (s : TS.sequent)
  : euf_param
  =
  let fail () =
    soft_failure ~loc:hyp_loc
      (Tactics.Failure "can only be applied on an hypothesis of the form \
checksign(m, s, pk(k)), hash(m, k) = t, or the symmetric equality")
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
          | Name _ as k when Symbols.is_ftype f Symbols.Hash table ->
            Some {ep_key=Name.of_term k; ep_intmsg=m; ep_term=t';
                  ep_int_f=f; ep_pk_f=None}
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
            match Theory.check_signature table f g, 
                  NO.expand_macro_check_all info tk with
            | Some sg, (Name _ as k) ->
              {ep_key= Name.of_term k; ep_intmsg=m; ep_term=s;
               ep_int_f=sg; ep_pk_f=Some g}
            | _ -> fail ()
          end
        | _ -> fail ()
      end
    | _ -> fail ()
                   

(*------------------------------------------------------------------*)
let euf
    (h : lsymb)
    (s : sequent)
  : sequent list
  =
  (* find parameters *)
  let _, hyp = Hyps.by_name h s in
  let contx = TS.mk_trace_cntxt s in
  let env = TS.env s in
  
  let {ep_key=k; ep_intmsg=m; ep_term=t; ep_int_f=int_f; ep_pk_f=pk_f} =
    euf_param ~hyp_loc:(L.loc h) contx hyp s
  in
      
  
  let pp_k ppf () = Fmt.pf ppf "%a" Name.pp k in

  (* apply euf *)
  let get_bad : ((term * Name.t, unit) NO.f_fold_occs) = 
    get_bad_occs env m k int_f ~pk_f 
  in
  let phis_bad, phis_int =
    NO.occurrence_formulas ~mode:PTimeNoSI ~pp_ns:(Some pp_k)
      integrity_formula
      get_bad contx env (t :: m :: k.Name.args)
  in
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
      (* XXX depends on Prover_state *)
      ProverLib.get_oracle_tag_formula (Symbols.to_string int_f)
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
      | Type.(Message, Message) -> 
        let f = 
          Term.subst [
            ESubst (Term.mk_var uvarm,m);
            ESubst (Term.mk_var uvarkey, Term.mk_name k.symb k.args);]
            f 
        in
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

