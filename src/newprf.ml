(* PRF equiv tactic *)
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


(* hash occurrence: store the hashed message and the key *)
(* same as int_occs in euf.ml, but I think it's clearer to keep them
   separate *)
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
(* Look for occurrences using NameOccs *)

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
  
  (* variables quantified above the current point are considered deterministic,
     so we add them to the env usd for "is_ptime_deducible" *)
  let env =
    Env.update ~vars:(Vars.add_vars (Vars.Tag.global_vars ~const:true fv) env.vars) env
  in
  match t with
  (* deterministic term -> no occurrences needed *)
  | _ when HighTerm.is_ptime_deducible ~const:`Exact ~si:false env t -> ([], [])
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
  | Fun (f, _, [Tuple [m'; Name (ksb',kargs') as k']])
    when f = hash_f && ksb'.s_symb = k.symb.s_symb ->
    let occs, accs = rec_call (m' :: kargs') in
    occs, accs @ [mk_hash_occ m' m (Name.of_term k') k  cond fv (fst info) st]

  | _ -> retry_on_subterms ()


(* constructs the formula expressing that a hash occurrence h(m',k')
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



(* to do move this somewhere else *)
(* some functions are copied from indcca.ml. VERY UGLY THIS IS BAD *)


(** Checks that there is no diff or binder in t above any name
    with the same symbol as n.
    Does not unfold any macro (meant to be used after rewriting
    in indcca_param, so we know that no occurrence of n can be
    under a macro) *)
let rec check_nodiffbind (n:Name.t) (t:term) : bool =
  if not (ER.has_name n t) then true
  else
    match t with
    | Diff (Explicit _) -> false
    | _ when Term.is_binder t -> false
    | _ -> Term.tforall (check_nodiffbind n) t


(** returns true iff f is a symmetric or asymmetric encryption function *)
let is_hash (table:Symbols.table) (f:Symbols.fname) =
  Symbols.(is_ftype f Hash table)

(** Returns true iff t contains an encryption function.
    does not unfold macros. *)
let rec has_hash (table:Symbols.table) (t:term) : bool =
  match t with
  | Term.Fun (f, _, _) when is_hash table f -> true
  | _ -> Term.texists (has_hash table) t


(** Returns true iff t contains a name w/ the same symbol as n.
    Does not unfold macros. *)
let rec has_name (n:Name.t) (t:term) : bool =
  match t with
  | Term.Name (ns, _) when ns.s_symb = n.symb.s_symb -> true
  | _ -> Term.texists (has_name n) t

(** Checks that each term ti in ts is f(argsi) for the same f,
    if so returns f and the list [args1;…;argsn]. 
    Does the same if each ti is Tuple(argsi). *)
let same_head_function (ts:Term.terms) :
  ((Symbols.fname * Type.ftype) option * Term.terms list) option =
  let rec aux ts f =
    match ts, f with
    | [], _ -> f
    | (Term.Fun (fs', ft', args))::ll, Some (Some (fs, ft), largs)
      when fs = fs' && ft = ft' ->
      aux ll (Some (Some (fs, ft), args::largs))
    | (Term.Fun (fs, ft, args))::ll, None ->
      aux ll (Some (Some (fs, ft), [args]))
    | (Term.Tuple args)::ll, Some (None, largs) ->
      aux ll (Some (None, args::largs))
    | (Term.Tuple args)::ll, None ->
      aux ll (Some (None, [args]))
    | _ -> None
  in
  aux (List.rev ts) None

(** Moves any diff that is above a hash function down
    as much as possible, stopping once it gets under the hash.
    Also moves diffs under tuples. *)
(* TODO this is very ad hoc this is bad *)
let rec move_diff_hash (table:Symbols.table) (t:term) : term =
  match t with
  | Diff (Explicit l) ->
    let (lp, lt) = List.split l in
    begin
      match same_head_function lt with
      | Some (Some (fs, ft), largs) when has_hash table t ->
        (* diff over a function -> move it under
           (only if there is still a hash below) *)
        let largs = List.megacombine largs in
        let largs = List.map
            (fun args -> Term.mk_diff (List.combine lp args))
            largs
        in
        let t = Term.mk_fun0 fs ft largs in
        Term.tmap (move_diff_hash table) t

      | Some (None, largs) ->
        (* diff over a tuple -> move it under *)
        let largs = List.megacombine largs in
        let largs = List.map
            (fun args -> Term.mk_diff (List.combine lp args))
            largs
        in
        let t = Term.mk_tuple largs in
        Term.tmap (move_diff_hash table) t

      | _ -> Term.tmap (move_diff_hash table) t
    end
  | _ -> Term.tmap (move_diff_hash table) t
      
  

(*------------------------------------------------------------------*)
(** PRF tactic *)

(** parameters for the prf tactic *)
type prf_param = { (* info on the h(m,k) we want to apply prf to *)
  pp_hash_f  : Symbols.fname;     (* hash function *)
  pp_key     : Term.term;         (* hash key *)
  pp_msg     : Term.term;         (* hashed message m *)
  pp_context : Term.term;         (* context around the hash *)
  pp_cname   : Name.t;            (* fresh name standing in for the
                                     hash in the context *)
  pp_table   : Symbols.table;     (* updated table with an entry xc *)
}


(** Finds the parameters of the prf application when no pattern selecting the
    hash to use is specified *)
let prf_param_nopattern
    ~(loc:L.t)
    (t:Term.term)    (* element in the goal where we want to apply prf *)
    (s:sequent)    
  : prf_param
  = 
  let table = ES.table s in
  let secontx = ES.system s in
  let sys = ES.get_system_pair s in 
  let hyps = ES.get_trace_hyps s in
  let t = move_diff_hash table t in (* move the diffs under the hashes,
                                            as much as possible *)

  (* rw_rule trying to rewrite an instance of f(xm,xk) into n_PRF *)
  (* use "Tuple [xm;xk]" to retrieve the value of vars once instantiated *) 
  let mk_rewrule
      (f:Symbols.fname)
      (hty:Type.ty) (mty:Type.ty) (kty:Type.ty) :
    Rewrite.rw_rule * Symbols.table * Name.t =
    let nprfdef = Symbols.{n_fty = Type.mk_ftype [] [] hty} in
    let table, nprfs =
      Symbols.Name.declare table (L.mk_loc L._dummy "n_PRF") nprfdef
    in
    let nprf = Name.{symb=Term.mk_symb nprfs hty; args=[]} in
    let xm = Vars.make_fresh mty "M" in
    let xk = Vars.make_fresh kty "K" in
    {rw_tyvars = [];
     rw_system = SE.to_arbitrary sys;
     rw_vars   = Vars.Tag.local_vars [xm; xk];
     (* local information, since we allow to match diff operators *)
     
     rw_conds  = [mk_eq ~simpl:false
                   (mk_tuple [mk_var xm; mk_var xk])
                   mk_false];
     rw_rw     = (mk_fun_tuple table f [mk_var xm; mk_var xk]),
                 (Name.to_term nprf);},
    table,
    nprf  in
  
  (* go through all hash functions, try to find a hash in the term *)
  let res = Symbols.Function.fold
      (fun f _ _ x -> (* for all functions:*)
         match x with
         | None when is_hash table f ->
           (* f is a hash symbol: try to find a ctxt *)
           let fty, _ = Symbols.Function.get_def f table in
           let hty = fty.fty_out in
           let mty, kty =
             match fty.fty_args with
             | [Type.Tuple [x;y]] -> x,y
             | _ -> assert false
           in
           
           let rule, table, nprf = mk_rewrule f hty mty kty in
           let res =
             Rewrite.rewrite
               table
               Vars.empty_env
               (* only local variables, hence [env] is useless here *)

               secontx InSequent hyps TacticsArgs.Once
               rule
               Equiv.(Global (Atom (Equiv [t])))
           in
           begin
             match res with
             | Rewrite.RW_Result rr -> Some (f, rr, table, nprf)
             | _ -> None
           end           
         | _ -> x) (* already found, or f is another function *)
      None
      table
  in

  match res with
  | None -> (* no hash was rewritten *)
    soft_failure ~loc (Tactics.Failure "no hash found")
      
  | Some (hash_f, (ccc, [(_, l)]), table, nprf) -> (* a hash was found *)

    (* get the context *)
    let cc =
      match (Equiv.any_to_equiv ccc) with
      | Equiv.(Atom (Equiv [cc])) -> cc
      | _ -> assert false
    in
                  
    (* get the content of variables from the conditions *)
    let m, k =
      match l with
      | Term.(Fun (ff, _, [Tuple [m; k]; fff])) when
          ff = Term.f_eq && fff = Term.mk_false ->
        m, k
      | _ -> assert false
    in

    (* only thing left is checking there's no diff or binders
       above nprf in cc *)
    if not (check_nodiffbind nprf cc) then 
      soft_failure ~loc
        (Tactics.Failure 
           "no diff or binder allowed above the hash for prf");
    (* return the parameters *)
    {pp_hash_f=hash_f; pp_key=k; pp_msg=m; pp_context=cc;
     pp_cname=nprf; pp_table=table}

  | _ -> assert false




(** Finds the parameters of the prf application when a pattern selecting the
    hash to use is specified
    (the pattern is in fact a term, as it gets instantiated before
    it's given to the tactic)
    Fails if the given pattern is not a hash *)
(* THIS IS NOT PRETTY TODO FACTOR THIS WITH THE PREVIOUS FUNCTION *)
let prf_param_withpattern
    ~(loc:L.t)
    (t:Term.term)    (* element in the goal where we want to apply prf *)
    (p:Term.term)    (* (supposedly) the hash to use *)
    (s:sequent)    
  : prf_param
  = 
  let table = ES.table s in
  let secontx = ES.system s in
  let sys = ES.get_system_pair s in 
  let hyps = ES.get_trace_hyps s in
  let t = move_diff_hash table t in (* move the diffs under the hashes,
                                            as much as possible *)
  

  (* check that the pattern p is indeed a hash, extract the msg and key *)
  let hash_f, hty, m, k =
    match p with
    | Term.Fun (hash_f, hty, [Tuple [m; k]])
      when is_hash table hash_f ->
      hash_f, hty.fty_out, m, k
    | _ -> soft_failure ~loc
             (Tactics.Failure "the pattern given to prf is not a hash")
  in

  (* generate a new name n_PRF to replace the hash with *)
  let nprfdef = Symbols.{n_fty = Type.mk_ftype [] [] hty} in
  let table, nprfs =
    Symbols.Name.declare table (L.mk_loc L._dummy "n_PRF") nprfdef
  in
  let nprf = Name.{symb=Term.mk_symb nprfs hty; args=[]} in

  (* rewrite rule trying to rewrite p into n_PRF *)
  (* (useful in case several occs of p are in t. maybe not very
     relevant, but it was already like that for the nopattern
     case, so why not *)
  let rule =
    Rewrite.{rw_tyvars = [];
     rw_system = SE.to_arbitrary sys;
     rw_vars   = [];
     rw_conds  = [];
     rw_rw     = p, Name.to_term nprf;}
  in

  (* rewrite it *)
  let res =
    Rewrite.rewrite
      table
      Vars.empty_env
      (* only local variables, hence [env] is useless here *)
      secontx InSequent hyps TacticsArgs.Once
      rule
      Equiv.(Global (Atom (Equiv [t])))
  in
  let cc = (* the context around the hash in t *)
    match res with
    | Rewrite.RW_Result (rr, _) ->
      (match (Equiv.any_to_equiv rr) with
       | Equiv.(Atom (Equiv [cc])) -> cc
       | _ -> assert false)
    |_ -> soft_failure ~loc
            (Tactics.Failure "no instance of the pattern found")
            
  in
  
  (* only thing left is checking there's no diff or binders
       above n_PRF in cc *)
  if not (check_nodiffbind nprf cc) then 
    soft_failure ~loc
      (Tactics.Failure 
         "no diff or binder allowed above the hash for prf");
  (* return the parameters *)
  {pp_hash_f=hash_f; pp_key=k; pp_msg=m; pp_context=cc;
   pp_cname=nprf; pp_table=table}
  



(** Constructs the formula expressing that in the proj
    of (the biframe + the context cc, the message m, the key k):
    - the proj of k is correctly used
    - the message m is not hashed anywhere else. *)
let phi_proj
    ?(use_path_cond=false)
    (loc     : L.t)
    (env     : Env.t)
    (contx   : Constr.trace_cntxt)
    (hash_f   : Symbols.fname)
    (biframe : terms)
    (cc      : term)   (* context above the hash in the goal *)
    (m       : term)
    (k       : term)
    (xc      : Name.t) (* stand-in for the ciphertext in cc. *)
    (proj    : proj)
  : Term.terms
  =
  (* project everything *)
  let system_p = SE.project [proj] contx.system in
  let env = Env.update ~system:{ env.system with set = (system_p :> SE.arbitrary); } env in
  let contx_p = { contx with system = system_p } in
  let cc_p = Term.project1 proj cc in
  let m_p = Term.project1 proj m in
  
  (* check that the key, once projected,is a name. *)
  let k_p = 
    match Term.project1 proj k with
    | Name _ as kp -> 
      Name.of_term kp
    | _ -> soft_failure ~loc
             (Tactics.Failure "Can only be applied on a hash where\
                               the key is a name")
  in
  let frame_p = List.map (Term.project1 proj) biframe in

  let pp_k ppf () = Fmt.pf ppf "%a" Name.pp k_p in

  (* get the bad key occs, and the messages hashed,
     in frame + cc + m + kargs *) 
  let get_bad = get_bad_occs env m_p k_p hash_f in

  let phi_k, phi_hash =
    NO.occurrence_formulas ~use_path_cond ~mode:PTimeSI ~negate:true ~pp_ns:(Some pp_k)
      hash_formula
      get_bad contx_p env
      (cc_p :: m_p :: k_p.args @ frame_p)
  in
  
  (* finally, fail if the generated formula contains the context's hole,
     ie name xc.
     TODO it should be possible to handle that case, see how. *)

  let phi = phi_k @ phi_hash in
  
  if List.exists (has_name xc) phi then
    soft_failure ~loc (Tactics.Failure "Bad context, generated formula has holes");

  phi


(*------------------------------------------------------------------*)
(** The PRF tactic  *)
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
       pp_context=cc; pp_cname=xc; pp_table=tablexc} =
    match p with
    | None -> prf_param_nopattern ~loc e s
    | Some p -> prf_param_withpattern ~loc e p s
  in
  let contxxc = {contx with table=tablexc} in

  let phi_proj =
    phi_proj ~use_path_cond:false loc env contxxc hash_f biframe cc m k xc 
    (* FEATURE: allow the user to set [use_path_cond] to true *)
  in


  Printer.pr "@[<v 0>Checking for side conditions on the left@; @[<v 0>";
  let phi_l = phi_proj proj_l in
          
  Printer.pr "@]@,Checking for side conditions on the right@; @[<v 0>";
  let phi_r = phi_proj proj_r in
  Printer.pr "@]@]@;";

  (* Removing duplicates. We already did that for occurrences, but
     only within phi_l and phi_r, not across both *)
  let cstate = Reduction.mk_cstate contx.table in
  let phis =
    Utils.List.remove_duplicate
      (Reduction.conv cstate) (phi_l @ phi_r)
  in

  let phi = Term.mk_ands ~simpl:true phis in

  (* no need to substitute xc in cc: it is already a name called n_PRF *)
  (* only need to add it the table containing it to s, in the equiv case *)
  let new_biframe = List.rev_append before (cc::after) in
  [ES.set_reach_goal phi s; ES.set_equiv_goal new_biframe (ES.set_table tablexc s)]

  

(*------------------------------------------------------------------*)
let prf_tac arg =
  match arg with
  | Args.(Pair (Int i, Opt (Message, p))) ->
    (match p with
     | None -> prf i None
     | Some (Message (p, _)) -> prf i (Some p))
  | _ -> assert false


let () =
  T.register_typed "newprf"
    ~general_help: "Apply the PRF axiom."
    ~detailed_help: "It allows to replace a hash h(m,k) by a name,\
                     provided a proof obligation stating that the key k is only\
                     used as a hash key, and is not hashed anywhere else.\
                     Behaves similarly to the fresh tactic."
    ~usages_sorts: []
    ~tactic_group: Cryptographic
    ~pq_sound:true
    (LT.genfun_of_pure_efun_arg prf_tac)
    Args.(Pair (Int, Opt Message))
