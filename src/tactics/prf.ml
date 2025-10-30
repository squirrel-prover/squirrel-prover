(* PRF equiv tactic *)
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
module CP = ComputePredicates

type sequent = ES.sequent

module MP = Match.Pos
module Sp = MP.Sp

(*------------------------------------------------------------------*)
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
(** Instantiating the occurrence search module *)
(* This is the same instantiation we use for EUF. (except the print function)
   In the beginning it seemed clearer to keep a copy here, rather
   than put it in a separate module called by both EUF and PRF.
   Maybe not though? *)

module O = Occurrences
module Name = O.Name
type name = Name.t


(** We search at the same time for bad ocurrences of the key, and for
    hashed messages (with a key) *)
type integrity_content =
  | BadKey of name
  | IntegrityMsg of {msg:Term.term; key:name}


module IntegrityOC : O.OccurrenceContent with type content = integrity_content
                                          and type data = unit =
struct
  type content = integrity_content
  type data = unit

  let collision_formula ~(negate : bool)
      ~(content : content) ~(collision : content) ~(data:unit)
    : Term.term
    =
    let _ = data in
    match content, collision with
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

  let pp_content ppe fmt x =
    match x with
    | BadKey k -> Fmt.pf fmt "%a" (Name.pp ppe) k
    | IntegrityMsg im ->
      Fmt.pf fmt "%a hashed by %a" (Term._pp ppe) im.msg (Name.pp ppe) im.key

  let pp_data _ppe fmt () : unit =
    Fmt.pf fmt ""
end

module IOC = IntegrityOC
module IOS = O.MakeSearch (IOC)
module IOF = O.MakeFormulas (IOS.EO)
let mk_simple_occ = IOS.EO.SO.mk_simple_occ



(*------------------------------------------------------------------*)
(* Two utility functions used when searching for the
   parameters of the tactic *)

(** Checks that there is no binder in t above any name
    with the same symbol as n.
    Does not unfold any macro (meant to be used after substituting
    in prf_param, so we know that no occurrence of n (n_PRF) can be
    hidden in a macro) *)
let rec no_binders_above (n:Name.t) (t:term) : bool =
  if Term.is_binder t then
    not (Name.has_name n t)
  else
    Term.tforall (no_binders_above n) t


(** Returns true iff f is declared as a hash function *)
let is_hash (table:Symbols.table) (f:Symbols.fname) =
  Symbols.OpData.(is_abstract_with_ftype f Hash table)

(*------------------------------------------------------------------*)
(** Look for occurrences using the Occurrences module *)

(** A IOS.f_fold_occs function.
    Looks for
    1) bad occurrences of the key k: places where a key with the same symbol
       as k is used other than in key position
    2) occurrences of hashed messages, with a key that has
       the same symbol as k. *)
let get_bad_occs
    (m:term)
    (k:Name.t)
    (hash_f:Symbols.fname) (* hash function *)
    ~(retry : unit -> IOS.simple_occs)
    ~(rec_call : O.pos_info -> Term.term -> IOS.simple_occs)
    (info:O.pos_info)
    (t:term) 
  : IOS.simple_occs =
  (* handles a few cases, using rec_call_on_subterm for rec calls,
     and calls retry_on_subterm for the rest *)
  match t with
  (* occurrence of the hash key *)
  | Name (ksb', kargs') as k' when ksb'.s_symb = k.symb.s_symb ->
    (* generate an occ, and also recurse on kargs' *)
    let occs1 = List.concat_map (rec_call info) kargs' in
    let occ =
      mk_simple_occ
        ~content:(BadKey (Name.of_term k'))
        ~collision:(BadKey k)
        ~data:()
        ~vars:info.pi_vars
        ~cond:info.pi_cond
        ~typ:info.pi_occtype
        ~sub:info.pi_subterm
        ~show:Show
    in
    occ :: occs1

  (* hash occurrence: no key occ but record the message hashed *)
  | App (Fun (f, _), [Tuple [m'; Name (ksb',kargs') as k']])
    when f = hash_f && ksb'.s_symb = k.symb.s_symb ->
    let occs = List.concat_map (rec_call info) (m' :: kargs') in
    (* we add to the end here, it seems to produce goals
       in a more intuitive order *)
    occs @
    [ mk_simple_occ
        ~content:(IntegrityMsg {msg=m'; key=Name.of_term k'})
        ~collision:(IntegrityMsg {msg=m; key=k})
        ~data:()
        ~vars:info.pi_vars
        ~cond:info.pi_cond
        ~typ:info.pi_occtype
        ~sub:info.pi_subterm
        ~show:Show ] (* TODO do we actually want to print it? *)

  | _ -> retry ()




(*------------------------------------------------------------------*)
(** PRF equivalence tactic parameters *)

(** Find the first hash in the given term
    (not under binders, does not unfold macros) *)
let find_hash_no_pattern
    ?(loc:L.t option)
    ~(table:Symbols.table) 
    (t:Term.term) : Term.term =
  let rec find t =
    match t with
    | App (Fun (f,_), [Tuple [_; _]]) when is_hash table f -> Some t
    | _ when is_binder t -> None
    |_ -> Term.tfold
            (fun t' op -> 
               if op = None then find t' else op)
            t
            None
  in
  match find t with 
  | None -> soft_failure ?loc (Failure "no hash found");
  | Some t -> t


(** Finds an instance of pattern [pat] in term [t]
    (* mostly copied from [generalize1] in LowTactics *) 
    (* TO DO: avoid code duplication *) *)
let find_hash_pattern 
    ?(loc : L.t option)
    ?(ienv : Infer.env option)
    ~(env : Env.t)
    (pat : Term.term) 
    (t : Term.term) :
  Term.term =

  (* are there any _ in [pat]? *)
  let no_term_holes = Sv.for_all (not -| Vars.is_hole) (Term.fv pat) in
  let ty_subst_opt =
    obind
      (fun ienv ->
         match Infer.close env ienv with
         | Infer.Closed s -> Some s
         | _ -> None)
      ienv
  in
  (* If there are no term holes and type holes can be inferred, we
         are done. *)
  if no_term_holes && ty_subst_opt <> None then
    Term.gsubst (oget ty_subst_opt) pat
      
  (* Otherwise, try to infer term and type variables by matching in t *)
  else
    let target = Equiv.Local t in
    let occurrences =
      HighTacticsArgs.occurrences_of_pat ~concrete:false ?ienv env pat ~target
    in
    if occurrences = [] then
      soft_failure ?loc (Failure "no occurrence of the pattern found");
    List.hd occurrences


(** Finds a hash on which to apply prf in the given term,
    using the pattern if one is provided. *)
let find_hash
  ?(loc : L.t option)
  ~(env : Env.t) 
  ~(table : Symbols.table)
  ?(opat : (Term.term * L.t option * Infer.env option) option)
  (t : Term.term) :
  Term.term =
  match opat with 
  | Some (p, _, ienv) -> find_hash_pattern ?loc ?ienv ~env p t
  | None -> find_hash_no_pattern ?loc ~table t



(** parameters for the prf tactic *)
type prf_param = { (* info on the h(m,k) we want to apply prf to *)
  pp_hash_f       : Symbols.fname;     (* hash function *)
  pp_key          : Term.term;         (* hash key *)
  pp_msg          : Term.term;         (* hashed message m *)
  pp_context_nprf : Term.term;         (* context around the hash *)
  pp_nprf         : Name.t;            (* fresh name standing in for the
                                          hash in the context *)
  pp_cond         : Term.term * Term.term;
  (* a pair of conditions expressing that
     on the left (resp. right), the condition above
     at least one of the occurrences of the hash in the term
     is satisfied.
     When looking at proof obligations we may assume 
     that condition holds, since otherwise nothing happens. *)
  pp_table        : Symbols.table;     (* updated table with an entry nprf *)
}


(** subst_term ~cond u v t returns t where instances of u are replaced with v
    1) except under binders
    2) not recursively
    3) collects the list of conditions above each replaced occurrence,
    with the corresponding system
    (each cond in the list returned is a list whose 'and'
     is the condition above one occ) *)    
let subst_term (se:SE.pair) (u:Term.term) (v:Term.term) (t:Term.term) : 
  Term.term * ((SE.fset * Term.terms) list) =
  let conds,_,t' =
    Match.Pos.map_fold ~mode:(`TopDown false)
      (fun t' se fv cond _ _info acc_conds ->
         assert (fv = []); (* sanity check: we never go under binders *)
         let se = SE.to_fset se in (* will always succeed *)
         if t' = u then (* found u: replace and add current condition to list *)
           (se,cond)::acc_conds, `Map v
         else if is_binder t' then (* t' is a binder: 
                                      stop there for this branch *)
           acc_conds, `Map t'
         else (* keep going *)
           acc_conds, `Continue)
      (se :> SE.arbitrary)
      []
      t
  in
  t', conds


(** Takes a projection, and a list of (system, condition list),
    selects the elements where the proj is in the system, and returns
    the 'or' of the 'and' of each element. 
    Each element is meant to be the list of conditions whose 'and' is the 
    condition above an occurrence of the has we replace, either on one 
    or both sides depending on the system. 
    So we select a side with proj, and compute a term saying 
    'the condition above at least one of the occurrences on that side holds'.*)
let project_conditions
    (proj:Projection.t) (conds:(SE.fset * Term.terms) list) : Term.term =
  let conds_p =
    List.filter_map
      (fun (se, cond) ->
         let projs = SE.to_projs se in
         (* when we'll use it, 
            projs will always be either a pair or a singleton *)
         if List.mem proj projs then 
           (* this condition applies to the side we're looking at:
              keep its 'and' *)
           let cond_p = List.map (Term.project1 proj) cond in
           Some (Term.mk_ands ~simpl:true cond_p)
         else 
           (* the condition is for an occurrence on the other side: ignore it *)
           None)
      conds
  in
  Term.mk_ors ~simpl:true conds_p



(** Finds the parameters of the prf application for equivalence goals,
    optionally using a pattern *)
let prf_param
    ~(loc:L.t)
    ?(opat : (Term.term * L.t option * Infer.env option) option)
    (t:Term.term)    (* element in the goal where we want to apply prf *)
    (s:sequent)    
  : prf_param
  = 
  let table = ES.table s in
  let sys = ES.get_system_pair s in
  let env = ES.env s in

  let p = find_hash ~loc ?opat ~table ~env t in

  (* check that p is indeed a hash, extract the msg and key *)
  let hash_f, hty, m, k =
    match p with
    | Term.App (Fun (hash_f, hty), [Tuple [m; k]])
      when is_hash table hash_f ->
      hash_f, hty.fty.fty_out, m, k
    | _ -> soft_failure ~loc
             (Tactics.Failure "prf only applies to hashes")
  in

  (* generate a new name n_PRF to replace the hash with *)
  let n_fty = Type.mk_ftype [] [] hty in
  let nprfdef = Symbols.Name { n_fty = n_fty ; n_sty = Symbols.Wrong } in
  let sn_prf = L.mk_loc L._dummy "n_PRF" in
  let table, nprfs =
    Symbols.Name.declare ~approx:true table sn_prf ~data:nprfdef
  in
  let table = Lemma.add_namelength_axiom table nprfs n_fty in
  let nprf = Name.{symb=Term.nsymb nprfs hty; args=[]} in

  (* replace instances of p with n_PRF, everywhere in t *)
  (* t_nprf is both the context in which prf will be applied,
     and the term left in the remaining proof goal afterwards *)
  let t_nprf, sysconds = subst_term sys p (Name.to_term nprf) t in

  (* sanity check: there's no diff or binders above n_PRF in t_nprf *)
  assert (no_binders_above nprf t_nprf);

  (* we may assume, when considering generated proof obligations on one side,
     that at least one replacement was performed on that side. 
     That assumption is computed here *)
  let proj_l,_ = SE.fst sys in
  let proj_r,_ = SE.snd sys in
  let cond_l = project_conditions proj_l sysconds in
  let cond_r = project_conditions proj_r sysconds in

  (* return the parameters *)
  {pp_hash_f=hash_f; pp_key=k; pp_msg=m; pp_context_nprf=t_nprf;
   pp_nprf=nprf; pp_cond=(cond_l,cond_r); pp_table=table}


(*------------------------------------------------------------------*)
(** PRF formula *)

type oracle_mode = Normal | Unreachable | Equality | Ignore
let _ = Equality

(** Constructs the formula expressing that in
    [terms], [terms_no_adv], [msg], and the indices of [key]:
    - [key] is correctly used (only as hash key)
    - the message [msg] is not hashed with [key].

    When [under_hash] is set to [true], ignores occurrences of hashes
    inside [msg] (the message being hashed in PRF), though occs of [key] are 
    still recorded. This option is useful when dealing with non-deduction goals.

    When [oracle] is set to anything other than [Normal],
    ignores the occurrences of a hash
    caused by the presence of a hash oracle [lambda x. (hash x key)] in [terms],
    and generates instead (if such an oracle was indeed present)
    a proof obligation, which is the second return value 
    of the function:
    - the formula [terms *> msg],if [oracle=Unreachable];
    - the formula [terms |> lambda x. x = msg], if [oracle=Equality];
    - nothing, if [oracle=Ignore].
    [terms_no_adv] is meant to contain terms in which we wish 
    to search for occurrences, but which are not given to the adversary, and 
    thus oracles there are not ignored. 

    Fails if the resulting formula still contains the optional [nprf].
    That is useful in the equivalence case: since we apply PRF under a context,
    the formula could contain a hole (represented by [nprf]).
    That case could be handled similarly to what's done in IND-CCA,
    but it is complicated and the usefulness is unclear.
    Alternately, we could find syntactic conditions on cc_nprf that guarantee
    this won't happen, but again it's unclear whether that's useful. *)
let phi_prf
    ?(use_path_cond=false)
    ?(under_hash=true)  (* do we also look for occurrences
                           in the m being hashed *)
    ?(oracle=Normal)  (* finer handling of the hashing oracle *)
    ?(nprf : Name.t option)  (* a name which must not appear in the 
                                resulting formula. typically, the n_prf
                                which stands for the hash in the context. *)
    (loc : L.t)
    (context : ProofContext.t)
    ~(hash_f : Symbols.fname)  (* hash function symbol *)
    ~(terms : Term.terms)  (* terms in which to look for occurrences *)
    ~(terms_no_adv : Term.terms)  (* terms in which we must also look for 
                                     occurrences, but which are not given
                                     to the adversary and thus not concerned
                                     by [oracle] *)
    ~(msg : Term.term)  (* message hashed *)
    ~(key : Term.term)  (* key *)
  : Term.terms * CP.form option
  =
  let env = context.env in
  let ppe = default_ppe ~table:env.table () in

  (* check that the key is a name *)
  let k = match key with
    | Name _ as k -> Name.of_term k
    | _ -> soft_failure ~loc
             (Tactics.Failure "Can only be applied on a hash where \
                               the key is a name.")
  in
  
  (* check if a term is in fact the oracle lambda x. h(x,k) *)
  let is_oracle (t:term) =
    match t with
    | Quant (Lambda, [x], Term.App
                           (Term.Fun (f, _), [Term.Tuple [y; k']]))
      when f = hash_f &&
           Term.equal y (mk_var x) &&
           Term.equal k' key ->
      true
    | _ -> false
  in
  

  (* pretty printer for the occurrence search *)
  let pp_k ppf () = 
    Fmt.pf ppf "bad occurrences of key %a,@ and messages hashed by it" 
      (Name.pp ppe) k
  in

  (* first construct the IOS.folds_occs *)
  let get_bad = get_bad_occs msg k hash_f in
  
  (* function to check whether an occ is a key occ or hash occ *)
  let is_key_occ x =
    match IOS.EO.(x.eo_occ.SO.so_cnt) with
    | BadKey _ -> true
    | IntegrityMsg _ -> false
  in

  (* get the bad key occs, and the messages hashed *)

  (* the messages where we look for occurrences *)
  (* if [under_hash] is set to false, we ignore [msg]
     and handle it separately *)
  (* in addition we ignore the oracle in [terms] if [oracle<>Normal] *)
  let terms_occ = 
    if oracle <> Normal then List.filter (fun x -> not (is_oracle x)) terms
    else terms
  in
  let terms_occ = k.args @ terms_occ @ terms_no_adv in
  let terms_occ = if under_hash then msg :: terms_occ else terms_occ in


  let occs =
    IOS.find_all_occurrences ~concrete:false ~mode:PTimeSI ~pp_descr:(Some pp_k)
      get_bad context terms_occ
  in
  
  let occs =
    if under_hash then occs
    else 
      (* Search separately in [msg], and there only keep key occs. *)
      let occs_m = 
        IOS.find_all_occurrences ~concrete:false ~mode:PTimeSI ~pp_descr:(Some pp_k)
          get_bad context [msg]
      in
      let occs_m = List.filter is_key_occ occs_m in
      occs_m @ occs 
  in


  (* sort the occurrences: first the key occs, then the hash occs *)
  let occs_key, occs_hash = List.partition is_key_occ occs in
  let occs = occs_key @ occs_hash in

  (* compute the formulas stating that none of the occs is a collision *)
  let phi = 
    List.map (IOF.occurrence_formula env ~use_path_cond:use_path_cond ~negate:true) occs
  in

  (* finally, fail if the generated formula contains the context's hole,
     ie name nprf.
     TODO it should be possible to handle that case? *)
  let _ =
    match nprf with 
    | None -> ()
    | Some nprf ->
      if List.exists (Name.has_name nprf) phi then
        soft_failure ~loc
          (Tactics.Failure 
             "The hash was in a bad context, the generated formula has holes")
  in
  
  (* additional (non-)deduction goal, when oracle is Unreachable or Equality *)
  let ded_goal =
    match oracle with
    | Unreachable when List.exists is_oracle terms ->
      Some (CP.make 
              env.table CP.NotDeduce
              (SE.to_fset env.system.set)
              ~left_tys:(List.map Term.ty terms)
              ~right_ty:(Term.ty msg)
              ~left:terms 
              ~right:msg)
    | Equality when List.exists is_oracle terms ->
      let xv = Vars.make_fresh (Term.ty msg) "x" in
      let x = Term.mk_var xv in
      let eqtest = Term.mk_quant Term.Lambda [xv] (Term.mk_eq x msg) in 
      Some (CP.make
              env.table CP.Deduce
              (SE.to_fset env.system.set)
              ~left_tys:(List.map Term.ty terms)
              ~right_ty:(Term.ty eqtest)
              ~left:terms
              ~right:eqtest)
    | _ -> None
  in
  phi, ded_goal



(** Projects on projs, and then calls phi_prf *)
let phi_prf_proj
    ?(use_path_cond=false)
    ?(under_hash=true)       (* do we also look for occurrences
                                in the m being hashed *)
    ?(oracle=Normal)          (* finer handling of the hashing oracle *)
    ?(nprf : Name.t option)  (* a name which must not appear in the 
                                resulting formula. typically, the n_prf
                                which stands for the hash in the context. *)
    (loc : L.t)
    (context : ProofContext.t)
    ~(hash_f : Symbols.fname)  (* hash function symbol *)
    ~(terms : Term.terms)  (* terms in which to look for occurrences *)
    ~(terms_no_adv : Term.terms)  (* terms in which we must also look for 
                                     occurrences, but which are not given
                                     to the adversary and thus not concerned
                                     by [oracle] *)
    ~(msg : Term.term)  (* message hashed *)
    ~(key : Term.term)  (* key *)
    (projs : Projection.t list)
  : Term.terms * CP.form option
  =
  let env = context.env in  
  let se = SE.project projs env.system.set in
  let new_system = { env.system with set = (se :> SE.arbitrary); } in
  let context = ProofContext.change_system ~system:new_system context in
  
  let terms = List.map (Term.project projs) terms in
  let terms_no_adv = List.map (Term.project projs) terms_no_adv in
  let msg = Term.project projs msg in 
  let key = Term.project projs key in

  phi_prf ~use_path_cond ~under_hash ~oracle ?nprf 
    loc context ~hash_f ~terms ~terms_no_adv ~msg ~key
  



(*------------------------------------------------------------------*)
(** The PRF tactic *)

(** PRF on an equivalence goal. *)
(* [oracle] should only be set to Normal until we know whether
   other modes are sound *)
let prf_equiv
    (i:int L.located)
    ?(opat : (Term.term * L.t option * Infer.env option) option)
    ?(oracle:oracle_mode=Normal)
    (s:sequent) : sequent list =
  
  let loc = L.loc i in

  (* TODO I disabled this for now, maybe it's still sound though *)
  if oracle <> Normal then
    soft_failure ~loc
      (Tactics.Failure "Unsupported oracle mode");

  if not (ES.conclusion_is_equiv s) then 
    soft_failure ~loc 
      (Tactics.Failure "Expected equivalence goal");

  let ppe = default_ppe ~table:(ES.table s) () in
  let env = ES.env s in

  let proj_l, proj_r = ES.get_system_pair_projs s in
  let system = ((Utils.oget env.system.pair) :> SE.fset) in

  let before, e, after, bound = LT.split_equiv_conclusion i s in
  let concrete = bound <> None in
  let biframe = List.rev_append before after in

  (* FEAT: concrete logic for equivalences *)
  if concrete then
    soft_failure
      (Tactics.GoalBadShape "concrete equivalence logic not yet implemented");

  (* get the parameters, enforcing that
     cc does not contain diffs or binders above xc.
     (at least the diff part could maybe be relaxed?) *)
  let {pp_hash_f=hash_f; pp_key=k; pp_msg=m;
       pp_context_nprf=cc_nprf; 
       pp_nprf=nprf; pp_cond=(cond_l,cond_r); pp_table=table_nprf} =
    prf_param ~loc ?opat e s
  in
  (* let context = {context with table=table_nprf} in *)
  
  Printer.pr
    "@[<v 0>Applying PRF to %a@;@;"
    (Term._pp ppe) (Term.mk_fun table_nprf hash_f [Term.mk_tuple [m;k]]);  

  let phi_prf_proj p =
    let se = SE.project [p] system in
    let new_system = { env.system with set = (se :> SE.arbitrary); } in
    let context = ES.proof_context ~in_system:new_system s in
    
    phi_prf_proj ~use_path_cond:false ~under_hash:true ~oracle ~nprf loc
      context ~hash_f 
      ~terms:(cc_nprf::biframe) ~terms_no_adv:[] ~msg:m ~key:k [p]
      (* FEATURE: allow the user to set [use_path_cond] to true *)
      
  in
  
  Printer.pr "@[<v 0>Checking for occurrences on the left@; @[<v 0>";
  (* get proof obligation for occurrences *)
  let phi_l, nded_l = phi_prf_proj proj_l in

  Printer.pr "@]@,Checking for occurrences on the right@; @[<v 0>";
  (* get proof obligation for occurrences *)
  let phi_r, nded_r = phi_prf_proj proj_r in

  Printer.pr "@]@]@;";

  (* add the assumption that the condition of at least one occ holds *)
  (* we'll ask to prove cond_l => phi_l on the left
     and similarly on the right *)
  (* when cond_l = cond_r (typically = true), we can factor a little:
     the intersection of phi_l and phi_r can be proved directly on both sides *)
  let phi_l, phi_r, phi_lr =
    if Term.alpha_conv cond_l cond_r then
      let inter = List.filter (fun u -> List.exists (Term.alpha_conv u) phi_r) phi_l in
      let phi_l = List.diff phi_l inter in
      let phi_r = List.filter (fun u -> not (List.exists (Term.alpha_conv u) inter)) phi_r in
      Term.mk_impl ~simpl:true cond_l (Term.mk_ands ~simpl:true phi_l),
      Term.mk_impl ~simpl:true cond_r (Term.mk_ands ~simpl:true phi_r),
      Term.mk_impl ~simpl:true cond_l (Term.mk_ands ~simpl:true inter)
      (* cond_l = cond_r *)
    else 
      Term.mk_impl ~simpl:true cond_l (Term.mk_ands ~simpl:true phi_l),
      Term.mk_impl ~simpl:true cond_r (Term.mk_ands ~simpl:true phi_r),
      Term.mk_true
  in


  (* goals:
     - phi_l in the previous sequent on the left system
     - phi_r in the previous sequent on the right system
     - if needed, phi_lr in the previous sequent
     - if [oracle], the secrecy subgoals generated by each phi
       (no need to change the system, as it's included in the secrecy predicate)
     - frame with t replaced with cc_nprf, with the updated table *) 
  let oldcontext = ES.system s in
  let oldpair = oget (oldcontext.pair) in

  let left = (SE.of_list [SE.fst oldpair] :> SE.arbitrary) in
  let left_sequent =
    ES.set_conclusion_in_context {oldcontext with set=left} (Equiv.mk_reach_atom phi_l) s
  in

  let right = (SE.of_list [SE.snd oldpair] :> SE.arbitrary) in
  let right_sequent =
    ES.set_conclusion_in_context {oldcontext with set=right} (Equiv.mk_reach_atom phi_r) s
  in
  let leftright = (oldpair :> SE.arbitrary) in
  let leftright_sequent =
    ES.set_conclusion_in_context {oldcontext with set=leftright} (Equiv.mk_reach_atom phi_lr) s
  in

  (* remove trivial goals *)
  let tracegoals = 
    List.filter 
      (fun x -> ES.conclusion x <> Equiv.mk_reach_atom Term.mk_true)
      [left_sequent; leftright_sequent; right_sequent]
  in

  (* non-deduction sequents (currently unused) *)
  let nded_sequents =
    match oracle with
    | Unreachable ->
      let mk_nded nd =
        match nd with 
        | None -> []
        | Some nd -> [ES.set_conclusion (CP.to_global nd) s]
      in
      List.concat_map mk_nded [nded_l; nded_r]
    | _ -> []           
  in

  let new_biframe = List.rev_append before (cc_nprf::after) in
  let equiv_sequent = ES.set_equiv_conclusion {terms= new_biframe; bound = None} (ES.set_table table_nprf s) in
  (* FEAT: concrete logic for equivalences *)


  (* copied from old prf for the composition stuff *)
  (* not sure how this works *)
  let tag_f =
    match Oracle.get_oracle hash_f (ES.table equiv_sequent) with
    | None -> []
    | Some oracle_formula ->
      let uvarm, uvarkey, f =
        match oracle_formula with
        | Quant (ForAll, [uvarm;uvarkey], f) -> uvarm,uvarkey,f
        | _ -> assert false
      in
      match Vars.ty uvarm, Vars.ty uvarkey with
      | Type.(Message, Message) ->
        let f =
          Term.subst [
            ESubst (Term.mk_var uvarm, m);
            ESubst (Term.mk_var uvarkey, k);] f
        in

        [ES.set_conclusion_in_context
           {oldcontext with set=leftright}
           (Equiv.mk_reach_atom (Term.mk_not f)) s]

      | _ -> assert false
  in


  tag_f @ tracegoals @ nded_sequents @ [equiv_sequent]



(** PRF for secrecy goals.
   In a sequent with a conclusion [u *>{S} v], sees [u] as [u1, th, u2]
   or [v] as [v1, th, v2] (depending on [side]), where [th=h(m,k)] is the [i]-th
   element. Fails if that element is not a hash.
   Returns the sequent with an updated conclusion [u1, u2 *> v] (if [Left])
   or closes the goal (if [Right]),
   and adds all proof obligations required by [prf].
   This is done by checking that [u1, u2, v] (left) or [u] (right)
   does not hash [m] with [k] and correctly uses [k].
   [m] itself must also correctly use [k],
   and if [under_hash] then we further check that it does not hash itself.
    
   If [u1, u2] (left) or [u] (right) contain a hash oracle [lambda x. h(x,k)],
   and [oracle <> Normal], the corresponding occurrence is ignored,
   and a subgoal may be added, depending on [oracle] and [side]:
    - [u1, u2 |> lambda x. x = m] if [oracle=Equality] and [side=Left];
    - [u1, u2 *> m] if [oracle=Unreachable] and [side=Left];
    - [u *> m] if [oracle=Unreachable] and [side=Right];
    - nothing, if [oracle=Ignore] and [side=Left].
    ([oracle=Equality] or [Ignore] are currently forbidden
    with [side=Right].)
*)
let prf_secrecy
    ~(side:CP.side)
    ~(oracle:oracle_mode)
    ~(under_hash:bool)
    (i:int L.located)
    (s:sequent)
  : sequent list =
  let ppe = default_ppe ~table:(ES.table s) () in
  let loc = L.loc i in
  let table = ES.table s in

  (* prevent forbidden oracle modes on the right *)
  if side = CP.Right && oracle <> Normal && oracle <> Unreachable then
    soft_failure ~loc
      (Tactics.Failure "Unsupported oracle mode");

  (* find the system in the secrecy predicate *)
  let sgoal = ES.conclusion_as_computability s in
  
  let system = CP.system sgoal in
  if not (SE.is_fset system) then
    soft_failure (Failure "the conclusion must be over a concrete system");
  let system = SE.to_fset system in
  
  (* hyps and trace context needed by phi_prf, with the same system *)
  let new_system = {(ES.system s) with set=(system :> SE.arbitrary)} in
  let context = ES.proof_context ~in_system:new_system s in  


  (* get the hash th (on the left or right), and the remaining terms us, vs *)
  let ii = L.unloc i in
  let us = CP.lefts sgoal in
  let vs = CP.rights sgoal in
  
  let th, us, vs = 
    try 
      match side with 
      | CP.Left ->
        let u1, th, u2 = List.splitat ii us in 
        th, (List.rev_append u1 u2), vs
      | CP.Right ->
        let v1, th, v2 = List.splitat ii vs in 
        th, us, (List.rev_append v1 v2)
    with 
    | List.Out_of_range ->
      soft_failure ~loc
        (Tactics.Failure 
           ("invalid position "^(string_of_int ii)^" in the conclusion"));
  in


  (* check that the term th is indeed a hash, get the key and hashed message *)
  let hash_f, msg, key =
    match th with
    | Term.App (Fun (hash_f, _), [Tuple [msg; key]])
      when is_hash table hash_f -> hash_f, msg, key
    | _ -> soft_failure ~loc
             (Tactics.Failure ("element "^(string_of_int ii)^" is not a hash"))
  in

  (* for prf left, we search for occs in [vs] but don't give it to the
     adversary. 
     for prf right, we ignore [vs] (since we'll show that the hash is secret 
     anyway). *)
  let terms_no_adv = if side = CP.Left then vs else [] in

  (* compute the prf formula + optional (non-)deduction goal. 
     note that we do not project here, and work directly on the predicate's set.
     that may cause the tactic to fail e.g. if the key was diff(k1, k2):
     in that case, project before applying the tactic? *)
  Printer.pr
    "@[<v 0>Applying PRF to %a@;@;"
    (Term._pp ppe) (Term.mk_fun table hash_f [Term.mk_tuple [msg;key]]);  
  let phi, nded =
    phi_prf ~use_path_cond:false ~under_hash ~oracle
      loc context ~hash_f 
      ~terms:us ~terms_no_adv ~msg ~key
  in
  Printer.pr "@]@;";

  (* reachability goal *)
  let phi = Term.mk_ands ~simpl:true phi in
  let reach_sequent =
    if not (Term.equal phi Term.mk_true) then 
      [ES.set_conclusion_in_context new_system (Equiv.mk_reach_atom phi) s]
    else 
      []
  in

  (* remaining secrecy goal [us *> vs], only for the left case *)
  let remaining_sgoal = CP.update_lefts us sgoal in
  let remaining_sequent =
    match side with 
    | CP.Left -> [ES.set_conclusion (CP.to_global remaining_sgoal) s]
    | CP.Right -> []
  in  

  (* non-deduction sequent *)
  let nded_sequent =
    match nded with 
    | None -> []
    | Some nded when (* when the additional non-deduction subgoal is the same
                        as the remaining sequent *)
           (CP.kind table nded = CP.kind table sgoal)
        && (Term.equal (CP.right sgoal) (CP.right nded))
        && (Term.equal (CP.left remaining_sgoal) (CP.left nded))
        && side = CP.Left ->
      []
    | Some nded
      -> [ES.set_conclusion (CP.to_global nded) s]
  in


  reach_sequent @ nded_sequent @ remaining_sequent






(*------------------------------------------------------------------*)
(** Parses the arguments and calls the appropriate version of PRF.
    TO DO: this is largely copied from fa and generalize… *)
let prf_tac (args : TacticsArgs.parser_args) (s:ES.t) =
  if ES.conclusion_is_equiv s then 
    match args with 
    | [TacticsArgs.Prf ([], i, opat)] ->
      let opat =
        omap 
          (fun p ->
             let ienv = Infer.mk_env () in
             let cenv = Typing.{env = ES.env s; cntxt = InGoal; } in
             let a, _ty =
               Typing.convert ~option:{Typing.Option.default with pat=`Holes}
                 ~ienv cenv p
             in
             (a, Some (L.loc p), Some ienv))
          opat
      in
      prf_equiv i ?opat s
    | _ -> LowTactics.bad_args ()

  else if ES.conclusion_is_computability s &&
          CP.kind (ES.table s) (ES.conclusion_as_computability s) 
          = CP.NotDeduce 
  then 
    match args with 
    | [TacticsArgs.Prf (nargs, i, None)] ->
      let fail loc =
        Tactics.hard_failure ~loc (Failure "incompatible arguments")
      in
      (* TODO this is ugly *)
      let oracle, under_hash, side =
        List.fold_left
          (fun (oracle, under_hash, side) narg ->
             match narg with
             | Args.NArg L.{ pl_loc = loc; pl_desc = "left" } -> 
               if side = None then 
                 oracle, under_hash, Some CP.Left
               else fail loc

             | Args.NArg L.{ pl_loc = loc; pl_desc = "right" } -> 
               if side = None then 
                 oracle, under_hash, Some CP.Right
               else fail loc

             | Args.NArg L.{pl_loc = loc; pl_desc = "normal_oracle"} ->
               if oracle = None then
                 Some Normal, under_hash, side
               else fail loc

             | Args.NArg L.{pl_loc = loc; pl_desc = "unreachable"} ->
               if oracle = None then
                 Some Unreachable, under_hash, side
               else fail loc

             | Args.NArg L.{pl_loc = loc; pl_desc = "equality"} ->
               if oracle = None then
                 Some Equality, under_hash, side
               else fail loc

             | Args.NArg L.{pl_loc = loc; pl_desc = "ignore_oracle"} ->
               if oracle = None then
                 Some Ignore, under_hash, side
               else fail loc

             | Args.NArg L.{pl_loc = loc; pl_desc = "under_hash"} ->
               if under_hash = None then
                 oracle, Some true, side
               else fail loc

             | Args.NList (l,_) 
             | Args.NArg  l     ->
               Tactics.hard_failure ~loc:(L.loc l) (Failure "unknown argument"))
          (None, None, None)
          nargs 
      in
      let oracle = oget_dflt Unreachable oracle in
      let under_hash = oget_dflt false under_hash in
      let side = oget_dflt CP.Right side in
      prf_secrecy ~side ~oracle ~under_hash i s
    | _ -> LowTactics.bad_args ()

  else 
    LowTactics.bad_args ()


let () =
  T.register_general "prf"
    (LT.gentac_of_etac_arg (fun x -> LowTactics.wrap_fail (prf_tac x)))
