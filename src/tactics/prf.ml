(* PRF equiv tactic *)
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

module Name = NameOccs.Name

type sequent = ES.sequent


module MP = Match.Pos
module Sp = MP.Sp


(*------------------------------------------------------------------*)

let soft_failure = Tactics.soft_failure

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
    not (ER.has_name n t)
  else
    Term.tforall (no_binders_above n) t


(** Returns true iff f is declared as a hash function *)
let is_hash (table:Symbols.table) (f:Symbols.fname) =
  Symbols.(is_ftype f Hash table)



(*------------------------------------------------------------------*)


(** Hash occurrence: store the hashed message and the key.
    (Same as int_occs in euf.ml, but I think it's clearer to keep them
    separate) *)
type hash_occ = ((term * Name.t), unit) NO.simple_occ
type hash_occs = hash_occ list

let mk_hash_occ
    (t:term) (tcoll:term) (k:Name.t) (kcoll:Name.t)
    (cond:terms) (fv:Vars.vars) (ot:NO.occ_type) (st:term) :
  hash_occ =
  let fv, sigma = Term.refresh_vars fv in
  let cond = List.map (Term.subst sigma) cond in
  let ot = NO.subst_occtype sigma ot in
  let t = Term.subst sigma t in
  let k = Name.subst sigma k in
  let st = subst sigma st in
  NO.mk_simple_occ (t,k) (tcoll,kcoll) () fv cond ot st



(*------------------------------------------------------------------*)
(** Look for occurrences using NameOccs *)
let get_bad_occs
    (env : Env.t)
    (m:term)
    (k:Name.t)
    (hash_f:Symbols.fname) (* hash function *)
    (retry_on_subterms : (unit -> NO.n_occs * hash_occs))
    (rec_call_on_subterms :
       (fv:Vars.vars ->
        cond:terms ->
        p:MP.pos ->
        info:NO.expand_info ->
        st:term ->
        term ->
        NO.n_occs * hash_occs))
    ~(info:NO.expand_info)
    ~(fv:Vars.vars)
    ~(cond:terms)
    ~(p:MP.pos)
    ~(st:term)
    (t:term) 
  : NO.n_occs * hash_occs =
  (* handles a few cases, using rec_call_on_subterm for rec calls,
     and calls retry_on_subterm for the rest *)
  (* only use this rec_call shorthand if the parameters don't change! *)
  let rec_call ?(st = st) = (* rec call on a list *)
    List.flattensplitmap (rec_call_on_subterms ~fv ~cond ~p ~info ~st)
  in
  
  (* variables quantified above the current point are considered constant,
     so we add them to the env usd for "is_ptime_deducible" *)
  let env =
    Env.update ~vars:(Vars.add_vars (Vars.Tag.global_vars ~const:true fv) env.vars) env
  in
  match t with
  (* deterministic term -> no occurrences needed *)
  | _ when HighTerm.is_ptime_deducible ~si:false env t -> ([], [])
  (* SI not needed here *)

  (* non ptime deterministic variable -> forbidden *)
  (* (this is where we used to check variables were only timestamps or indices) *)
  | Var v ->
    soft_failure
      (Tactics.Failure (Fmt.str "terms contain a non-ptime variable: %a" Vars.pp v))

  (* occurrence of the hash key *)
  | Name (ksb', kargs') as k' when ksb'.s_symb = k.symb.s_symb ->
    (* generate an occ, and also recurse on kargs' *)
    let occs1, accs1 = rec_call kargs' in
    (NO.mk_nocc (Name.of_term k') k fv cond (fst info) st) :: occs1,
    accs1

  (* hash occurrence: no key occ but record the message hashed *)
  | App (Fun (f, _), [Tuple [m'; Name (ksb',kargs') as k']])
    when f = hash_f && ksb'.s_symb = k.symb.s_symb ->
    let occs, accs = rec_call (m' :: kargs') in
    occs, accs @ [mk_hash_occ m' m (Name.of_term k') k  cond fv (fst info) st]

  | _ -> retry_on_subterms ()


(** Constructs the formula expressing that a hash occurrence h(m',k')
    is indeed in collision with h(m, k) *)
let hash_formula
    ~(negate : bool)
    ((m', k') : term * Name.t)
    ((m, k) : term * Name.t)
    ()
    : term =
  (* every occurrence we generated should satisfy this *)
  assert (k.symb.s_symb = k'.symb.s_symb); 

  if not negate then 
    mk_and
      (mk_eqs ~simpl:true ~simpl_tuples:true k.args k'.args)
      (mk_eq ~simpl:true m m')
  else
    mk_impl
      (mk_eqs ~simpl:true ~simpl_tuples:true k.args k'.args)
      (mk_neq ~simpl:true m m')



  

(*------------------------------------------------------------------*)
(** PRF tactic *)

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
      (fun t' se fv cond _ acc_conds ->
         assert (fv = []); (* sanity check: we never go under binders *)
         let se = SE.to_fset se in (* will always succeed *)
         if t' = u then (* found u: replace and add current condition to list *)
           (se,cond)::acc_conds, `Map v
         else if is_binder t' then (* t' is a binder: stop there for this branch *)
           (se,cond)::acc_conds, `Map t'
         else (* keep going *)
           acc_conds, `Continue)
      (se :> SE.arbitrary)
      []
      t
  in
  t', conds
    

(** Takes a projection, and a list of (system, condition list),
    select the elements where the proj is in the system, and returns
    the 'or' of the 'and' of each element. 
    Each element is meant to be the list of conditions whose 'and' is the 
    condition above an occurrence of the has we replace, either on one 
    or both sides depending on the system. 
    So we select a side with proj, and compute a term saying 
    'the condition above at least one of the occurrences on that side holds'.*)
let project_conditions
    (proj:Term.proj) (conds:(SE.fset * Term.terms) list) : Term.term =
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



(** Finds the first hash in the term
   (not under binders, does not unfold macros) *)
let rec find_hash (table:Symbols.table) (t:Term.term) : Term.term option =
  match t with
  | App (Fun (f,_), [Tuple [_; _]]) when is_hash table f -> Some t
  | _ when is_binder t -> None
  |_ -> Term.tfold
          (fun t' op -> if op = None then find_hash table t' else op)
          t
          None


(** Finds the parameters of the prf application when a pattern selecting the
    hash to use is specified
    (the pattern is in fact a term, as it gets instantiated before
    it's given to the tactic)
    Fails if the pattern given is not a hash *)
let prf_param_pattern
    ~(loc:L.t)
    (t:Term.term)    (* element in the goal where we want to apply prf *)
    (p:Term.term)    (* (supposedly) the hash to use *)
    (s:sequent)    
  : prf_param
  = 
  let table = ES.table s in
  let sys = ES.get_system_pair s in

  (* check that the pattern p is indeed a hash, extract the msg and key *)
  let hash_f, hty, m, k =
    match p with
    | Term.App (Fun (hash_f, hty), [Tuple [m; k]])
      when is_hash table hash_f ->
      hash_f, hty.fty.fty_out, m, k
    | _ -> soft_failure ~loc
             (Tactics.Failure "the pattern given to prf is not a hash")
  in
  
  (* generate a new name n_PRF to replace the hash with *)
  let n_fty = Type.mk_ftype [] [] hty in
  let nprfdef = Symbols.{n_fty} in
  let sn_prf = (L.mk_loc L._dummy "n_PRF") in
  let table, nprfs =
    Symbols.Name.declare table sn_prf nprfdef
  in
  let real_name = L.mk_loc L._dummy (Symbols.to_string nprfs) in
  let table = Process.add_namelength_axiom table real_name n_fty in
  let nprf = Name.{symb=Term.mk_symb nprfs hty; args=[]} in

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
  
  
(** Finds the parameters of the prf application *)
let prf_param
    ~(loc:L.t)
    (t:Term.term)    (* element in the goal where we want to apply prf *)
    (op:Term.term option) (* optional: the hash we want to replace *)
    (s:sequent)
  : prf_param
  = 
  let table = ES.table s in
  let p =
    match op with
    | Some p -> p (* use the given pattern *)
    | None ->
      match find_hash table t with
      | Some p -> p (* find some hash in the term *)
      | None -> (* no usable hash in the term *)
        soft_failure ~loc (Tactics.Failure "no hash found")    
  in
  prf_param_pattern ~loc t p s



(** Constructs the formula expressing that in the proj
    of (the biframe + the context cc_nprf, the message m, the key k):
    - the proj of k is correctly used
    - the message m is not hashed anywhere else.
    Fails if the resulting formula still contains n_PRF.
    That case could be handled similarly to what's done in IND-CCA,
    but it is complicated and the usefulness is unclear.
    Alternately, we could find syntactic conditions on cc_nprf that guarantee
    this won't happen, but again it's unclear whether that's useful. *)
let phi_proj
    ?(use_path_cond=false)
    (loc     : L.t)
    (env     : Env.t)
    (contx   : Constr.trace_cntxt)
    (hash_f  : Symbols.fname)
    (biframe : Term.terms)
    (cc_nprf : Term.term)
    (m       : Term.term)
    (k       : Term.term)
    (nprf    : Name.t) (* stand-in for the hash in cc_nprf. *)
    (proj    : proj)
  : Term.terms
  =
  (* project everything *)
  let system_p = SE.project [proj] contx.system in
  let env =
    Env.update
      ~system:{ env.system with set = (system_p :> SE.arbitrary); }
      env
  in
  let contx_p = { contx with system = system_p } in
  let cc_nprf_p = Term.project1 proj cc_nprf in
  let m_p = Term.project1 proj m in
  
  (* check that the key, once projected, is a name. *)
  let k_p = 
    match Term.project1 proj k with
    | Name _ as kp -> 
      Name.of_term kp
    | _ -> soft_failure ~loc
             (Tactics.Failure "Can only be applied on a hash where \
                               the key is a name.")
  in
  let frame_p = List.map (Term.project1 proj) biframe in

  let pp_k ppf () = Fmt.pf ppf "%a" Name.pp k_p in

  (* get the bad key occs, and the messages hashed,
     in frame + cc + m + kargs *) 
  let get_bad = get_bad_occs env m_p k_p hash_f in

  let phi_k, phi_hash =
    NO.occurrence_formulas
      ~use_path_cond ~mode:PTimeSI ~negate:true ~pp_ns:(Some pp_k)
      hash_formula
      get_bad contx_p env
      (cc_nprf_p :: m_p :: k_p.args @ frame_p)
  in
  
  (* finally, fail if the generated formula contains the context's hole,
     ie name xc.
     TODO it should be possible to handle that case, see how. *)

  let phi = phi_k @ phi_hash in
  
  if List.exists (ER.has_name nprf) phi then
    soft_failure ~loc
      (Tactics.Failure "The hash was in a bad context, the generated formula has holes");

  phi


(*------------------------------------------------------------------*)
(** The PRF tactic *)
let prf (i:int L.located) (p:Term.term option) (s:sequent) : sequent list =
  let contx = ES.mk_pair_trace_cntxt s in
  let env = ES.env s in
  let loc = L.loc i in

  let proj_l, proj_r = ES.get_system_pair_projs s in

  let before, e, after = LT.split_equiv_goal i s in
  let biframe = List.rev_append before after in
  
  
  (* get the parameters, enforcing that
     cc does not contain diffs or binders above xc.
     (at least the diff part could maybe be relaxed?) *)
  let {pp_hash_f=hash_f; pp_key=k; pp_msg=m;
       pp_context_nprf=cc_nprf; pp_nprf=nprf; pp_cond=(cond_l,cond_r); pp_table=table_nprf} =
    prf_param ~loc e p s
  in
  let contx_nprf = {contx with table=table_nprf} in

  Printer.pr
    "@[<v 0>Applying PRF to %a@;@;"
    Term.pp (Term.mk_fun contx.table hash_f [Term.mk_tuple [m;k]]);  
  let phi_proj =
    phi_proj ~use_path_cond:false loc
      env contx_nprf hash_f biframe cc_nprf m k nprf 
    (* FEATURE: allow the user to set [use_path_cond] to true *)
  in

  Printer.pr "@[<v 0>Checking for bad use of the key on the left@; @[<v 0>";
  (* get proof obligation for occurrences *)
  let phi_l = phi_proj proj_l in
          
  Printer.pr "@]@,Checking for bad use of the key on the right@; @[<v 0>";
  (* get proof obligation for occurrences *)
  let phi_r = phi_proj proj_r in

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
     - frame with t replaced with cc_nprf, with the updated table *) 
  let oldcontext = ES.system s in
  let oldpair = oget (oldcontext.pair) in

  let left = (SE.of_list [SE.fst oldpair] :> SE.arbitrary) in
  let left_sequent =
    ES.set_goal_in_context {oldcontext with set=left} (Equiv.mk_reach_atom phi_l) s
  in

  let right = (SE.of_list [SE.snd oldpair] :> SE.arbitrary) in
  let right_sequent =
    ES.set_goal_in_context {oldcontext with set=right} (Equiv.mk_reach_atom phi_r) s
  in
  let leftright = (oldpair :> SE.arbitrary) in
  let leftright_sequent =
      ES.set_goal_in_context {oldcontext with set=leftright} (Equiv.mk_reach_atom phi_lr) s
  in

  (* remove trivial goals *)
  let tracegoals = 
    List.filter 
      (fun x -> ES.goal x <> Equiv.mk_reach_atom Term.mk_true)
      [left_sequent; leftright_sequent; right_sequent]
  in
  
  let new_biframe = List.rev_append before (cc_nprf::after) in
  let equiv_sequent = ES.set_equiv_goal new_biframe (ES.set_table table_nprf s) in


  (* copied from old prf for the composition stuff *)
  (* not sure how this works *)
  
  (* XXX This get options refs from Prover 
   * → it depends on Prover state *)
  let oracle_formula =
    ProverLib.get_oracle_tag_formula (Symbols.to_string hash_f)
  in

  let tag_f =
    if Term.is_false oracle_formula then
      []
    else
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

        [ES.set_goal_in_context
           {oldcontext with set=leftright}
           (Equiv.mk_reach_atom (Term.mk_not f)) s]

      | _ -> assert false
  in

  
  tag_f @ tracegoals @ [equiv_sequent]
  

(*------------------------------------------------------------------*)
let prf_tac arg =
  match arg with
  | Args.(Pair (Int i, Opt (Message, p))) ->
    (match p with
     | None -> prf i None
     | Some (Message (p, _)) -> prf i (Some p))
  | _ -> assert false


let () =
  T.register_typed "prf"
    ~general_help: "Apply the PRF axiom."
    ~detailed_help: "It allows to replace a hash h(m,k) by a name,\
                     provided a proof obligation stating that the key k is only\
                     used as a hash key, and m is not hashed anywhere else.\
                     Behaves similarly to the fresh tactic."
    ~usages_sorts: []
    ~tactic_group: Cryptographic
    ~pq_sound:true
    (LT.genfun_of_pure_efun_arg prf_tac)
    Args.(Pair (Int, Opt Message))
