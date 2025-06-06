open Utils
open Ppenv

module L = Location
module Args = TacticsArgs
module T = Tactics

module TopHyps = Hyps           (* alias, as we define another [Hyps] later *)
module SE = SystemExpr
module TS = LowTraceSequent

module Sid = Ident.Sid

(*------------------------------------------------------------------*)
(** {2 Hypotheses for equivalence sequents} *)

module H = Hyps.EquivHyps

let subst_hyps (subst : Term.subst) (hyps : H.hyps) : H.hyps =
  H.map
    ~hyp:(Equiv.subst subst) 
    ~def:(fun (se,t) -> se, Term.subst subst t) 
    hyps

let gsubst_hyps (subst : Subst.t) (hyps : H.hyps) : H.hyps =
  H.map
    ~hyp:(Equiv.gsubst subst) 
    ~def:(fun (se,t) -> SE.gsubst subst se, Term.gsubst subst t) 
    hyps

(*------------------------------------------------------------------*)
(** {2 Equivalence sequent} *)

type hyp_form = Equiv.form
type conc_form = Equiv.form

let hyp_kind = Equiv.Global_t
let conc_kind = Equiv.Global_t

(** default variable information of the sequent *)
let var_info = Vars.Tag.gtag
    
(** An equivalence sequent features:
    - a global formula as [conclusion];
    - a [proof_context] containing global formula hypotheses;
    - an environment [env] listing all free variables,
      and the systems to be used for interpreting formulas. *)
type t = {
  env           : Env.t;
  proof_context : H.hyps;
  conclusion    : Equiv.form;
}

type sequent = t

type sequents = sequent list

(*------------------------------------------------------------------*)
(** variables that are free in the sequent, i.e. that must be bound by
    [s.vars]. *)
let fv (s : t) : Vars.Sv.t =
  let h_vars =
    H.fold (fun id ld vars ->
        match ld with
        | LHyp f     -> Vars.Sv.union (Equiv.fv f) vars
        | LDef (_,t) ->
          Vars.Sv.union (Term.fv  t) vars |>
          Vars.Sv.add (Vars.mk id (Term.ty t))
          (* a defined variable must be bound by [s.vars] *)
      ) s.proof_context Vars.Sv.empty
  in
  Vars.Sv.union h_vars (Equiv.fv s.conclusion)

(*------------------------------------------------------------------*)
let ty_fv (s : t) : Type.Fv.t =
  let h_vars =
    H.fold (fun _ ld vars ->
        match ld with
        | LHyp f     -> Type.Fv.union (Equiv.ty_fv f) vars
        | LDef (_,t) -> Type.Fv.union (Term.ty_fv  t) vars
      ) s.proof_context Type.Fv.empty
  in
  Type.Fv.union h_vars (Equiv.ty_fv s.conclusion)


(*------------------------------------------------------------------*)
(** The pretty-printing environment table [ppe.table] is always
    replaced by the table of the sequent. *)
let _pp ppe fmt j =
  let ppe = { ppe with table = j.env.table; } in
  let env_without_defined_vars =
    H.fold (fun id ld env ->
        match ld with
        | LDef (_,t) -> Vars.rm_var (Vars.mk id (Term.ty t)) env
        | _ -> env
      ) j.proof_context j.env.vars
  in
  Fmt.pf fmt "@[<v 0>" ;

  if not (j.env.se_vars = []) then
    Fmt.pf fmt "@[System variables: %a@]@;" 
      SE.pp_tagged_vars j.env.se_vars ;

  Fmt.pf fmt "@[Systems: %a@]@;"
    SystemExpr.pp_context j.env.system;

  if j.env.ty_vars <> [] then
    Fmt.pf fmt "@[Type variables: %a@]@;"
      (Fmt.list ~sep:Fmt.comma Type.pp_tvar) j.env.ty_vars ;

  if j.env.vars <> Vars.empty_env then
    Fmt.pf fmt "@[<hv 2>Variables:@ @[%a@]@]@;"
      (Vars._pp_env ppe) env_without_defined_vars ;

  H._pp ppe ~context:j.env.system fmt j.proof_context ;

  (* Print separation between hyps and conclusion *)
  Printer.kws `Separation fmt (String.make 40 '-') ;
  Fmt.pf fmt "@;%a@]"
    (Equiv._pp_conclusion ~context:j.env.system ppe) j.conclusion

let pp     = _pp (default_ppe ~dbg:false ())
let pp_dbg = _pp (default_ppe ~dbg:true  ())

(*------------------------------------------------------------------*)
let pp_init ppe fmt (j : sequent) =
  if j.env.vars <> Vars.empty_env then
    Fmt.pf fmt "forall %a,@ " (Vars._pp_env ppe) j.env.vars ;
  Fmt.pf fmt "%a" (Equiv._pp ppe) j.conclusion

(*------------------------------------------------------------------*)
let sanity_check (s : t) : unit =
  Vars.sanity_check s.env.Env.vars;

  (* all term variables are bound *)
  if not ((Vars.Sv.subset (fv s) (Vars.to_vars_set s.env.Env.vars))) then
    let () =
      Fmt.epr "Anomaly in LowEquivSequent.sanity_check:@.%a@.@." pp_dbg s
    in
    assert false
  else ();
      
  let tyfv = ty_fv s in
  (* all type variables are bound *)
  assert (Sid.subset tyfv.tv (Sid.of_list s.env.ty_vars));
  (* no univars remaining *)
  assert (Sid.subset tyfv.uv Sid.empty)

(*------------------------------------------------------------------*)
(** {2 Hypotheses functions} *)

(** Built on top of [H] *)
module Hyps
  : Hyps.S1 with type hyp  = Equiv.form 
             and type hyps := t
= struct
  
  type hyp       = Equiv.form 
  type 'a kind   = 'a H.kind
  type ldecl_cnt = H.ldecl_cnt
  type ldecl     = Ident.ident * ldecl_cnt
                 
  (*------------------------------------------------------------------*)  
  let pp_hyp = Equiv.pp

  let pp_ldecl     = H.pp_ldecl
  let pp_ldecl_dbg = H.pp_ldecl_dbg
  let _pp_ldecl    = H._pp_ldecl

  (*------------------------------------------------------------------*)  
  let fresh_id  ?approx name  s = H.fresh_id  ?approx name  s.proof_context
  let fresh_ids ?approx names s = H.fresh_ids ?approx names s.proof_context

  let is_hyp f s = H.is_hyp f s.proof_context

  let by_id id s = H.by_id id s.proof_context
  let by_id_k id k s = H.by_id_k id k s.proof_context

  let by_name id s = H.by_name id s.proof_context
  let by_name_k id k s = H.by_name_k id k s.proof_context

  let mem_id   id s = H.mem_id   id s.proof_context
  let mem_name id s = H.mem_name id s.proof_context

  let find_opt func s = H.find_opt func s.proof_context

  let find_map func s = H.find_map func s.proof_context

  let find_all func s = H.find_all func s.proof_context
      
  let to_list s = H.to_list s.proof_context

  let exists func s = H.exists func s.proof_context

  let _add ~(force:bool) id hyp s =
    let id, proof_context = H._add ~force id hyp s.proof_context in
    id, { s with proof_context }

  let add_i npat f s =
    let id, proof_context = H.add_i npat f s.proof_context in
    id, { s with proof_context }

  let add npat f s = { s with proof_context = H.add npat f s.proof_context }

  let add_i_list l (s : sequent) =
    let ids, proof_context = H.add_i_list l s.proof_context in
    ids, { s with proof_context }

  let add_list l s = { s with proof_context = H.add_list l s.proof_context }

  let remove id s = { s with proof_context = H.remove id s.proof_context }

  let iter func s = H.iter func s.proof_context

  let fold      func s init = H.fold      func s.proof_context init
  let fold_hyps func s init = H.fold_hyps func s.proof_context init

  let map  ?hyp ?def s = { s with proof_context = H.map  ?hyp ?def s.proof_context }
  let mapi ?hyp ?def s = { s with proof_context = H.mapi ?hyp ?def s.proof_context }

  let filter_map ?hyp ?def s =
    { s with proof_context = H.filter_map ?hyp ?def s.proof_context }

  let filter f s = { s with proof_context = H.filter f s.proof_context }

  let clear_triv s = { s with proof_context = H.clear_triv s.proof_context }

  let _pp ppe fmt s =
    let ppe = { ppe with table = s.env.table; } in
    H._pp ppe ~context:s.env.system fmt s.proof_context

  let pp     = _pp (default_ppe ~dbg:false ()) 
  let pp_dbg = _pp (default_ppe ~dbg:true  ())
end

(*------------------------------------------------------------------*)
(** {2 Accessors and utils} *)

let update ?table ?ty_vars ?vars ?hyps ?conclusion t =
  let env  = Env.update ?table ?ty_vars ?vars t.env
  and proof_context = Utils.odflt t.proof_context hyps
  and conclusion = Utils.odflt t.conclusion conclusion in
  { env; proof_context; conclusion; } 

let env j = j.env

let set_env env s = { s with env }

let vars j = j.env.vars

let set_vars vars j = update ~vars j

let system j = j.env.system

let set_conclusion_in_context ?update_local ?bound system conc s =

  assert (update_local = None);
 assert (bound = None);

  if system = s.env.system then { s with conclusion = conc } else

    (* Update hypotheses. *)
    let proof_context =
      TopHyps.change_equiv_hyps_context
        ~table:s.env.table
        ~vars:s.env.vars
        ~old_context:s.env.system
        ~new_context:system
        s.proof_context
    in
    (* Change the context in the sequent's environment. *)
    let env = Env.update ~system s.env in
    let s = { s with env; proof_context } in

    (* Finally set the new conclusion. *)
    { s with conclusion = conc }

let params s = Params.{ ty_vars = s.env.ty_vars; se_vars = s.env.se_vars; }

let table j = j.env.table
let set_table table j = update ~table j

let conclusion j = j.conclusion
let bound _ = assert false
let set_bound _ = assert false

let ty_vars j = j.env.ty_vars

let set_conclusion conclusion j = { j with conclusion }

let set_reach_conclusion f s = set_conclusion Equiv.(Atom (Reach {formula = f; bound = None})) s
  (*TODO:Concrete : Probably something to do to create a bounded goal*)

let get_frame proj j = match j.conclusion with
  | Equiv.Atom (Equiv.Equiv e) ->
    Some ({Equiv.terms = List.map (Term.project1 proj) e.terms; bound = None})
  (*TODO:Concrete : Probably something to do to create a bounded goal*)
  | _ -> None

(*------------------------------------------------------------------*)
let subst subst s =
  { s with conclusion = Equiv.subst subst s.conclusion;
           proof_context = subst_hyps subst s.proof_context; }

(*------------------------------------------------------------------*)
let gsubst (subst : Subst.t) s =
  if subst == Subst.empty_subst then s else
    let vars = Vars.map (fun v t -> Subst.subst_var subst v, t) s.env.vars in
    { env  = Env.update ~vars s.env;
      conclusion = Equiv.gsubst subst s.conclusion;
      proof_context = gsubst_hyps subst s.proof_context; }

(*------------------------------------------------------------------*)
let rename (u:Vars.var) (v:Vars.var) (s:t) : t =
  assert (not (Vars.mem s.env.vars v));
  let s = subst [Term.ESubst (Term.mk_var u, Term.mk_var v)] s in
  let info = Vars.get_info u s.env.vars in
  {s with
    env = Env.update
             ~vars:(Vars.add_var v info (Vars.rm_var u s.env.vars))
             s.env;}

(*------------------------------------------------------------------*)
let conclusion_is_equiv s = match conclusion s with
  | Atom (Equiv.Equiv _) -> true
  | _ -> false

let conclusion_as_equiv s = match conclusion s with
  | Atom (Equiv.Equiv e) when e.bound = None -> e
  (*TODO:Concrete : Probably something to do to create a bounded goal*)
  | _ ->
    Tactics.soft_failure (Tactics.GoalBadShape "expected an equivalence")

(*------------------------------------------------------------------*)
(** Convert global sequent to local sequent, assuming
    that the conclusion of the input sequent is a reachability formula. *)
let to_trace_sequent s =
  let env = s.env in

  let conclusion,bound = match s.conclusion with
    | Equiv.Atom (Equiv.Reach f) -> f.formula,f.bound
    | _ ->
      Tactics.soft_failure
        (Tactics.GoalBadShape "expected a reachability formula")
  in

  let trace_s = TS.init ~env ?bound conclusion in
  let trace_s =
  Hyps.fold
    (fun id ld trace_s ->
       match ld with
       | TopHyps.LHyp hyp ->
         TS.Hyps.add (Args.Named (Ident.name id)) (TopHyps.LHyp (Global hyp)) trace_s
       | TopHyps.LDef (se,t) -> 
         let id', trace_s = TS.Hyps._add ~force:true id (LDef (se,t)) trace_s in
         assert (Ident.equal id' id);
         trace_s
    ) s trace_s
    in 
    trace_s

(*------------------------------------------------------------------*)
let conclusion_is_computability (s : t) : bool =
  ComputePredicates.is_computability s.env.table s.conclusion

let conclusion_as_computability (s : t) : ComputePredicates.form =
  if not (ComputePredicates.is_computability s.env.table s.conclusion) then
    Tactics.soft_failure (Tactics.GoalBadShape "expected a computability goal");

  ComputePredicates.from_global s.env.table s.conclusion

(*------------------------------------------------------------------*)
let get_trace_hyps ?in_system s =
  TS.get_trace_hyps
    ?in_system
    (to_trace_sequent (set_reach_conclusion Term.mk_false s))

(*------------------------------------------------------------------*)
let get_models (system : 'a SE.expr option) (s : t) =
  let s = to_trace_sequent (set_reach_conclusion Term.mk_false s) in
  TS.get_models system s

let proof_context ?(in_system : SE.context option) (s : t) =
  let env =
    match in_system with
    | None -> s.env
    | Some system -> { s.env with system; }
  in
  ProofContext.make
    ~env
    ~hyps:(get_trace_hyps ~in_system:env.system s)

let pair_proof_context (s : sequent) : ProofContext.t =
  let in_system = 
    { s.env.system with set = (oget s.env.system.pair :> SE.t) ; } 
  in
  proof_context ~in_system s 
    
(*------------------------------------------------------------------*)
let query_happens ~precise (s : t) (a : Term.term) =
  let s = to_trace_sequent (set_reach_conclusion Term.mk_false s) in
  TS.query_happens ~precise s a


let check_pq_sound_sequent s =
  match conclusion s with
  | Atom (Equiv.Equiv e) ->
      let models = get_models None s in
      let cntxt = pair_proof_context s in
      if not (PostQuantum.is_attacker_call_synchronized cntxt models e.terms) then
  (*TODO:Concrete : Probably something to do to create a bounded goal*)
        Tactics.hard_failure Tactics.GoalNotPQSound
      else
        s
  | _ -> s

(*------------------------------------------------------------------*)
let set_equiv_conclusion e j =
  let new_sequent = set_conclusion Equiv.(Atom (Equiv e)) j in
  if TConfig.post_quantum (table j) then
   check_pq_sound_sequent new_sequent
  else new_sequent


let init ?(no_sanity_check=false) ~env ?(hyp : Equiv.form option) conclusion =
  let proof_context = H.empty in
  let proof_context = match hyp with
    | None -> proof_context
    | Some h ->
        snd (H._add ~force:false (H.fresh_id "H" proof_context) (LHyp h) proof_context)
  in
  let new_sequent = { env; proof_context; conclusion } in
  if not no_sanity_check then sanity_check new_sequent;

  if TConfig.post_quantum (env.table) then
   check_pq_sound_sequent new_sequent
  else new_sequent

let mem_felem i s =
  conclusion_is_equiv s &&
  i < List.length (conclusion_as_equiv s).terms
  (*TODO:Concrete : Probably something to do to create a bounded goal*)

let change_felem ?loc i elems s =
  try
    let before, _, after = List.splitat i (conclusion_as_equiv s).terms in
  (*TODO:Concrete : Probably something to do to create a bounded goal*)
    set_equiv_conclusion {terms = (List.rev_append before (elems @ after)); bound = None} s
  (*TODO:Concrete : Probably something to do to create a bounded goal*)
  with List.Out_of_range ->
    Tactics.soft_failure ?loc (Tactics.Failure "out of range position")


let get_felem ?loc i s =
  try
    let _, t, _ = List.splitat i (conclusion_as_equiv s).terms in t
  (*TODO:Concrete : Probably something to do to create a bounded goal*)
  with List.Out_of_range ->
    Tactics.soft_failure ?loc (Tactics.Failure "out of range position")

(*------------------------------------------------------------------*)
let get_system_pair t = oget (system t).pair

let get_system_pair_projs t : Projection.t * Projection.t =
  let p = get_system_pair t in
  fst (SE.fst p), fst (SE.snd p)

(*------------------------------------------------------------------*)
let check_conclusion_is_equiv (s : sequent) : unit =
  if not (Equiv.is_equiv (conclusion s)) then
    Tactics.soft_failure (Tactics.GoalBadShape "expected an equivalence")

(*------------------------------------------------------------------*)
module Conc  = Equiv.Smart
module Hyp   = Equiv.Smart
