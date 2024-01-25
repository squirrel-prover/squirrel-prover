(* EUF trace tactic *)
open Squirrelcore
open Term
open Utils

module Args = TacticsArgs
module L = Location
module SE = SystemExpr

module TS = TraceSequent

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
(* Instantiating the occurrence search module *)

module O = Occurrences
module Name = O.Name
type name = Name.t


(** We search at the same time for bad ocurrences of the key, and for
    protected (signed/hashed) messages (with a key) *)
type integrity_content =
  | BadKey of name
  | IntegrityMsg of {msg:Term.term; key:name}


module IntegrityOC : O.OccContent with type content = integrity_content
                                   and type data = unit =
struct
  type content = integrity_content
  type data = unit

  let collision_formula ~(negate : bool)
      (x : content) (xcoll : content) ()
    : Term.term
    =
    match x, xcoll with
    | BadKey k, BadKey kcoll ->
      (* sanity check: only apply when same symbol *)
      assert (k.symb = kcoll.symb);
      if not negate then
        Term.mk_eqs ~simpl:true ~simpl_tuples:true kcoll.args k.args
      else
        Term.mk_neqs ~simpl:false ~simpl_tuples:true kcoll.args k.args

    | IntegrityMsg im, IntegrityMsg imcoll ->
      (* sanity check: key must have same symbol in both messages *)
      assert (im.key.symb = imcoll.key.symb);
      if not negate then
        mk_and
          (mk_eq ~simpl:true imcoll.msg im.msg)
          (mk_eqs ~simpl:true ~simpl_tuples:true imcoll.key.args im.key.args)
      else
        mk_impl
          (mk_eqs ~simpl:true ~simpl_tuples:true imcoll.key.args im.key.args)
          (mk_neq ~simpl:true imcoll.msg im.msg)
    | _ ->
      (* sanity check: we should never record a collision between two things
         with a different constructor *)
      assert false

  let subst_content sigma x =
    match x with
    | BadKey k -> BadKey (Name.subst sigma k)
    | IntegrityMsg im -> IntegrityMsg  {msg=Term.subst sigma im.msg;
                                        key=Name.subst sigma im.key}

  let subst_data _ () = ()

  let pp_content fmt x =
    match x with
    | BadKey k -> Fmt.pf fmt "%a" Name.pp k
    | IntegrityMsg im ->
      Fmt.pf fmt "%a auth. by %a" Term.pp im.msg Name.pp im.key

  let pp_data fmt () : unit =
    Fmt.pf fmt ""
end

module IOC = IntegrityOC
module IOS = O.MakeSearch (IOC)
module IOF = O.MakeFormulas (IOS.EO)
let mk_simple_occ = IOS.EO.SO.mk_simple_occ


(*------------------------------------------------------------------*)
(* Look for occurrences using the Occurrences module *)

(** A [IOS.f_fold_occs] function.
    Looks for
    1) bad occurrences of the key [k]: places where a key with the same symbol
       as [k] is used other than in key position
    2) occurrences of protected (signed/hashed) messages, with a key that has
       the same symbol as [k]. *)
let get_bad_occs
    (env : Env.t)
    (m : Term.term)
    (k : name)
    (int_f : Symbols.fname) (* function with integrity (hash, signature) *)
    ?(pk_f : Symbols.fname option=None) (* public key function. Must be None iff hash *)
    (retry_on_subterms : unit -> IOS.simple_occs)
    (rec_call_on_subterms : O.pos_info -> Term.term -> IOS.simple_occs)
    (info : O.pos_info)
    (t : term) 
  : IOS.simple_occs
  =
  (* handles a few cases, using rec_call_on_subterm for rec calls,
     and calls retry_on_subterm for the rest *)

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
  (* (this is where we used to check variables were only timestamps or indices) *)
  | Var v ->
    soft_failure
      (Tactics.Failure (Fmt.str "terms contain a non-ptime variable: %a" Vars.pp v))

  (* occurrence of the signing/hash key *)
  | Name (ksb', kargs') as k' when ksb'.s_symb = k.symb.s_symb ->
    (* generate an occ, and also recurse on kargs' *)
    let occs1 = List.concat_map (rec_call_on_subterms info) kargs' in
    let oc =
      mk_simple_occ
        (BadKey (Name.of_term k'))
        (BadKey k)
        ()
        info.pi_vars
        info.pi_cond
        info.pi_occtype
        info.pi_subterm
    in
    oc :: occs1

  (* occurrence of the public key (for the signature case only) *)
  | App (Fun (f, _), [tk']) when pk_f = Some f -> (* public key *)
    begin
      match O.expand_macro_check_all (O.get_expand_info info) tk' with
      | Name (_, tkargs') ->
        List.concat_map (rec_call_on_subterms info) tkargs'
      (* pk(k'): no occ,
         even if k'=k, just look in k' args *)
      | _ -> retry_on_subterms () (* otherwise look in tk' *)
    end

  (* hash verification oracle: test u = h(m', k).
     Search recursively in u, m', kargs', but do not record
     m' as a hash occurrence. *)
  | App (Fun (f, _), [u; App (Fun (g, _), [Tuple [m'; Name (ksb', kargs')]])])
    when f = f_eq && g = int_f && pk_f = None && ksb'.s_symb = k.symb.s_symb ->
    List.concat_map
      (rec_call_on_subterms {info with pi_subterm=t}) (* we change the
                                                         subterm *)
      (u :: m' :: kargs')

  (* hash verification oracle (converse case h(m', k) = u). *)
  | App (Fun (f, _), [App (Fun (g, _), [Tuple [m'; Name (ksb', kargs')]]); u])
    when f = f_eq && g = int_f && pk_f = None && ksb'.s_symb = k.symb.s_symb ->
    List.concat_map
      (rec_call_on_subterms {info with pi_subterm=t})
      (u :: m' :: kargs') (* we change st here as well*)

  (* hash/sign/etc w/ a name that could be the right key *) 
  (* record this hash occurrence, but allow the key *)
  (* q: actually why don't we always do this,
               even if it's the wrong key?
     a: that would be sound but generate too many occs *)
  | App (Fun (f, _), [Tuple [m'; Name (ksb', kargs') as k']])
    when f = int_f && k.symb.s_symb = ksb'.s_symb ->
    let occs = List.concat_map (rec_call_on_subterms info) (m' :: kargs') in
    occs @
    [ mk_simple_occ
        (IntegrityMsg {msg=m'; key=Name.of_term k'})
        (IntegrityMsg {msg=m ; key=k})
        ()
        info.pi_vars info.pi_cond info.pi_occtype info.pi_subterm ]

  | _ -> retry_on_subterms ()



(*------------------------------------------------------------------*)
(** {2 EUF tactic} *)

(** parameters for the integrity occurrence: key, signed or hashed message,
    signature checked or compared w/ the hash, sign/hash function,
    pk function if any *) 
type euf_param = {
  ep_key    : Name.t;
  ep_intmsg : term;
  ep_term   : term;
  ep_int_f  : Symbols.fname;
  ep_pk_f   : Symbols.fname option;
}

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
  let einfo = O.EI_direct, contx in
  let table = contx.table in

  (* try to write hyp as u = v *)
  match TS.Reduce.destr_eq s Equiv.Local_t hyp with
  | Some (u, v) -> (* an equality: try to see u or v as h(m, k) *)
    let u = O.expand_macro_check_all einfo u in
    let v = O.expand_macro_check_all einfo v in
    let try_t (t:term) (t':term) : euf_param option =
      match t with
      | App (Fun (f, _), [Tuple [m; tk]]) ->
        begin
          match O.expand_macro_check_all einfo tk with
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
    match O.expand_macro_check_all einfo hyp with
    | App (Fun (f, _), [Tuple [m; s; tpk]]) ->
      begin
        match O.expand_macro_check_all einfo tpk with
        | App (Fun (g, _), [tk]) ->
          begin
            match Theory.check_signature table f g, 
                  O.expand_macro_check_all einfo tk with
            | Some sg, (Name _ as k) ->
              {ep_key= Name.of_term k; ep_intmsg=m; ep_term=s;
               ep_int_f=sg; ep_pk_f=Some g}
            | _ -> fail ()
          end
        | _ -> fail ()
      end
    | _ -> fail ()


(*------------------------------------------------------------------*)
let euf (h : lsymb) (s : sequent) : sequent list =
  (* find parameters *)
  let _, hyp = TS.Hyps.by_name_k h Hyp s in
  let hyp = as_local ~loc:(L.loc h) hyp in (* FIXME: allow global hyps? *)
  let contx = TS.mk_trace_cntxt s in
  let env = TS.env s in

  let {ep_key=k; ep_intmsg=m; ep_term=t; ep_int_f=int_f; ep_pk_f=pk_f} =
    euf_param ~hyp_loc:(L.loc h) contx hyp s
  in

  let pp_k ppf () =
    Fmt.pf ppf "bad occurrences of key %a,@ and messages authenticated by it" 
      Name.pp k
  in

  (* apply euf: first construct the IOS.f_fold_occs to use *)
  let get_bad : IOS.f_fold_occs = 
    get_bad_occs env m k int_f ~pk_f 
  in

  (* get all occurrences *)
  let occs =
    IOS.find_all_occurrences ~mode:PTimeNoSI ~pp_ns:(Some pp_k)
      get_bad
      (TS.get_trace_hyps s) contx env (t :: m :: k.Name.args)
  in

  (* sort the occurrences: first the key occs, then the integrity occs *)
  let occs_key, occs_int =
    List.partition
      (fun x ->
         match IOS.EO.(x.eo_occ.SO.so_cnt) with
         | BadKey _ -> true
         | IntegrityMsg _ -> false)
      occs
  in
  let occs = occs_key @ occs_int in

  (* compute the formulas stating that one of the occs is a collision *)
  let phis = List.map (IOF.occurrence_formula ~negate:false) occs in

  (* finally generate all corresponding goals *)
  let g = TS.conclusion s in 
  let integrity_goals =
    List.map
      (fun phi -> TS.set_conclusion (mk_impl ~simpl:false phi g) s)
      phis
  in

  (* copied from old euf, handles the composition goals *)
  let tag_s =
    let f =
      let loc_int_f = L.mk_loc (L.loc h) (Symbols.to_string int_f) in
      Oracle.get_oracle_tag_formula loc_int_f (TS.table s)
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
        [TS.set_conclusion
           (Term.mk_impl f (TS.conclusion s)) s]

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
    ~pq_sound:true
    (LowTactics.gentac_of_ttac_arg euf_tac)