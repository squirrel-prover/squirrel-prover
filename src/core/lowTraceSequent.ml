open Utils
open Ppenv

module L    = Location
module SE   = SystemExpr
module Args = TacticsArgs
module Sv   = Vars.Sv
module Sid  = Ident.Sid

open Hyps

(*------------------------------------------------------------------*)
type hyp_form = Equiv.any_form
type conc_form = Equiv.local_form

let hyp_kind = Equiv.Any_t
let conc_kind = Equiv.Local_t

(* default variable information of the sequent *)
let var_info = Vars.Tag.make Vars.Local

(*------------------------------------------------------------------*)
(* For debugging *)
let dbg ?(force=false) table s =
  let mode = if TConfig.debug_tactics table || force then `Dbg else `Ignore in
  Printer.prt mode s

(*------------------------------------------------------------------*)
module H = Hyps.TraceHyps

(*------------------------------------------------------------------*)
module S : sig
  type t = private {
    env : Env.t;
    
    proof_context : H.hyps;
    (** Hypotheses *)

    bound : Term.term option;
    (** Upper-bound *)

    conclusion : Term.term;
    (** The conclusion / right-hand side formula of the sequent. *)    
  }

  val pp     : t formatter
  val pp_dbg : t formatter
  val _pp    : t formatter_p

  val init_sequent :
    no_sanity_check:bool ->
    env:Env.t ->
    bound : Term.term option ->
    conclusion:Term.term ->
    t

  val fv : t -> Vars.Sv.t

  val sanity_check : t -> unit
                     
  val update :
    ?env:Env.t ->
    ?proof_context:H.hyps ->
    ?bound:Term.term ->
    ?conclusion:Term.term ->
    t -> t

end = struct
  type t = {
    env              : Env.t;
    proof_context   : H.hyps;
    bound : Term.term option;
    conclusion   : Term.term;
  }

  (** The pretty-printing environment table [ppe.table] is always
    replaced by the table of the sequent. *)
  let _pp ppe fmt s =
    let ppe = { ppe with table = s.env.table; } in
    let env_without_defined_vars = 
      H.fold (fun id ld env ->
          match ld with
          | LDef (_,t) -> Vars.rm_var (Vars.mk id (Term.ty t)) env
          | _ -> env
        ) s.proof_context s.env.vars
    in
    Fmt.pf fmt "@[<v 0>" ;

    if not (s.env.se_vars = []) then
      Fmt.pf fmt "@[System variables: %a@]@;" 
        SE.pp_tagged_vars s.env.se_vars;

    Fmt.pf fmt "@[System: %a@]@;"
      SystemExpr.pp_context s.env.system;

    if s.env.ty_vars <> [] then
      Fmt.pf fmt "@[Type variables: %a@]@;" 
        (Fmt.list ~sep:Fmt.comma Type.pp_tvar) s.env.ty_vars ;

    if s.env.vars <> Vars.empty_env then
      Fmt.pf fmt "@[<hv 2>Variables:@ @[%a@]@]@;"
        (Vars._pp_env ppe) env_without_defined_vars ;

    (* Print hypotheses *)
    H._pp ppe ~context:s.env.system fmt s.proof_context ;

    (* Print separation between proof_context and conclusion *)
    Printer.kws `Separation fmt (String.make 40 '-') ;

    (* Print conclusion formula and close box. *)
    match s.bound with
    | None -> Fmt.pf fmt "@;%a@]" (Term._pp ppe) s.conclusion
    | Some ve ->
      Fmt.pf fmt "@;%a@;bound : %a@]" (Term._pp ppe) s.conclusion (Term._pp ppe) ve

  let pp     = _pp (default_ppe ~dbg:false ())
  let pp_dbg = _pp (default_ppe ~dbg:true ())

  (** variables that are free in the sequent, i.e. that must be bound
      by [s.vars]. *)
  let fv (s : t) : Vars.Sv.t = 
    let h_vars = 
      H.fold (fun id ld vars -> 
          match ld with
          | LHyp f     -> Vars.Sv.union (Equiv.Any.fv f) vars
          | LDef (_,t) ->
            Vars.Sv.union (Term.fv      t) vars |>
            Vars.Sv.add (Vars.mk id (Term.ty t))
            (* a defined variable must be bound by [s.vars] *)
        ) s.proof_context Vars.Sv.empty
    in
    Vars.Sv.union
      (Vars.Sv.union h_vars (Term.fv s.conclusion))
      (omap_dflt Vars.Sv.empty Term.fv s.bound)

  let ty_fv (s : t) : Type.Fv.t =
    let h_vars =
      H.fold (fun _ ld vars ->
          match ld with
          | LHyp f     -> Type.Fv.union (Equiv.Any.ty_fv f) vars
          | LDef (_,t) -> Type.Fv.union (Term.ty_fv      t) vars
        ) s.proof_context Type.Fv.empty
    in
    Type.Fv.union
      (Type.Fv.union h_vars (Term.ty_fv s.conclusion))
      (omap_dflt Type.Fv.empty Term.ty_fv s.bound)

  (**TODO:Concrete: check that the possible variable in the bound are taken into account*)
  let sanity_check s : unit =
    Vars.sanity_check s.env.Env.vars;

    if not (Vars.Sv.subset (fv s) (Vars.to_vars_set s.env.Env.vars)) then
      let () =
        Fmt.epr "Anomaly in LowTraceSequent.sanity_check:@.%a@.@.\
                 Fail on %a @.not in %a @.@."
          pp_dbg s
          Vars.pp_list (Vars.Sv.elements (fv s))
          Vars.pp_list (Vars.Sv.elements (Vars.to_vars_set s.env.Env.vars))
      in
      assert false
    else ();

    let tyfv = ty_fv s in
    (* all type variables are bound *)
    assert (Sid.subset tyfv.tv (Sid.of_list s.env.ty_vars));
    (* no univars remaining *)
    assert (Sid.subset tyfv.uv Sid.empty)


  let init_sequent ~no_sanity_check ~(env : Env.t) ~bound ~conclusion =
    let proof_context = H.empty in
    let s = { env ; proof_context; bound; conclusion; } in
    if not no_sanity_check then sanity_check s;
    s

  let update ?env ?proof_context ?bound ?conclusion t =
    let env           = Utils.odflt t.env env
    and proof_context = Utils.odflt t.proof_context proof_context
    and bound = match t.bound, bound with
      | Some _, Some _ -> bound
      | Some _, None -> t.bound
      | None, None -> None
      | _ -> Tactics.soft_failure (Failure "Not a concrete local judement")
    and conclusion    = Utils.odflt t.conclusion conclusion in
    { env; proof_context; bound; conclusion; }
end

include S

type sequent = S.t
type sequents = sequent list

(*------------------------------------------------------------------*)
let get_trace_hyps ?in_system (s : sequent) =
  match in_system with
  | None -> s.proof_context
  | Some system ->
    Hyps.change_trace_hyps_context
      ~old_context:s.env.system ~new_context:system
      ~table:s.env.table ~vars:s.env.vars
      s.proof_context

(*------------------------------------------------------------------*)
let get_all_messages (s : sequent) =
  let atoms = List.map snd (Hyps.get_atoms_of_hyps s.proof_context) in
  (*TODO:Concrete : Probably something to here but not sure for now*)
  let atoms =
    Term.Lit.form_to_xatom s.conclusion :: atoms
  in
  List.fold_left (fun acc at ->
      match at with
      | Term.Lit.Happens _ -> acc
      | Term.Lit.Comp (_,a,b) -> a :: b :: acc
      | Term.Lit.Atom a -> a :: acc
    ) [] atoms

(*------------------------------------------------------------------*)
(** Prepare constraints or TRS query *)

let get_models (system : 'a SE.expr option) (s : sequent) =
  Hyps.get_models s.env.table ~system s.proof_context

(*------------------------------------------------------------------*)
(** General version of query, which subsumes the functions
    constraints_valid and query that will eventually be exported,
    and provides joint benchmarking support. *)

let query ?(system : 'a SE.expr option = None) ~precise s = function
  | None -> not (Constr.m_is_sat (get_models system s))
  | Some q -> Constr.query ~precise (get_models system s) q

module ConstrBenchmark = Benchmark.Make(struct
  type input =  SE.arbitrary option * bool * sequent * Term.terms option
  type output = bool
  let default =
    "Constr",
    (fun (system,precise,s,q) -> query ~system ~precise s q)
  let basename = "squirrel_bench_constr_"
  let pp_input ch (_,_,_,q) = match q with
    | None -> Format.fprintf ch "false"
    | Some q -> (Fmt.list ~sep:(Fmt.any ",@ ") Term.pp) ch q
  let pp_result ch = function
    | Ok b -> Format.fprintf ch "%b" b
    | Error _ -> Format.fprintf ch "fail"
end)

let register_query_alternative name alt =
  ConstrBenchmark.register_alternative
    name
    (fun (system,precise,s,q) -> alt ~system ~precise s q)

let query ?(system : SE.arbitrary option = None) ~precise s q =
  ConstrBenchmark.run (system,precise,s,q)

(** Exported versions of query and its alternatives. *)

let query_happens ~precise s a =
  query ~precise s (Some [Term.mk_happens a])

let constraints_valid ?(system : 'a SE.expr option = None) s =
  (* The precise flag is irrelevant in that case. *)
  query ~system ~precise:true s None

let query ?(system : SE.arbitrary option = None) ~precise s q =
   query ~system ~precise s (Some q)

(** Other uses of Constr *)

let maximal_elems ~precise s tss =
  let models = get_models None s in
  Constr.maximal_elems ~precise models tss

let get_ts_equalities ~precise s =
  let models = get_models None s in
  let ts = List.map (fun (_,x) -> x) (Hyps.get_trace_literals s.proof_context)
             |>  Atom.trace_atoms_ts in
  Constr.get_ts_equalities ~precise models ts

(*------------------------------------------------------------------*)  
module Hyps
  : Hyps.S1 with type hyp  = Equiv.any_form 
             and type hyps := t
= struct

  type hyp       = Equiv.any_form 
  type 'a kind   = 'a H.kind
  type ldecl_cnt = H.ldecl_cnt
  type ldecl     = Ident.ident * ldecl_cnt

  (*------------------------------------------------------------------*)  
  let pp_hyp = Equiv.pp_any_form

  let pp_ldecl     = H.pp_ldecl
  let pp_ldecl_dbg = H.pp_ldecl_dbg
  let _pp_ldecl    = H._pp_ldecl

  let fresh_id  ?approx name  s = H.fresh_id  ?approx name  s.proof_context
  let fresh_ids ?approx names s = H.fresh_ids ?approx names s.proof_context

  let is_hyp f s = H.is_hyp f s.proof_context

  let by_id id s = H.by_id id s.proof_context
  let by_id_k id k s = H.by_id_k id k s.proof_context

  let by_name id s = H.by_name id s.proof_context
  let by_name_k id k s = H.by_name_k id k s.proof_context

  let to_list s = H.to_list s.proof_context

  let mem_id   id s = H.mem_id   id s.proof_context
  let mem_name id s = H.mem_name id s.proof_context

  let find_opt func s = H.find_opt func s.proof_context

  let find_map func s = H.find_map func s.proof_context

  let find_all func s = H.find_all func s.proof_context
      
  let exists func s = H.exists func s.proof_context

  let _add ~(force:bool) id hyp s =
    let id, proof_context = H._add ~force id hyp s.proof_context in
    id, S.update ~proof_context s

  let add_i npat f s =
    let id, proof_context = H.add_i npat f s.proof_context in
    id, S.update ~proof_context s

  let add npat f s = S.update ~proof_context:H.(add npat f s.proof_context) s

  let add_i_list l (s : sequent) =
    let ids, proof_context = H.add_i_list l s.proof_context in
    ids, S.update ~proof_context s

  let add_list l s = snd (add_i_list l s)
  
  let remove id s = S.update ~proof_context:(H.remove id s.proof_context) s

  let iter func s = H.iter func s.proof_context

  let fold      func s init = H.fold      func s.proof_context init
  let fold_hyps func s init = H.fold_hyps func s.proof_context init

  let map  ?hyp ?def s = S.update ~proof_context:(H.map  ?hyp ?def s.proof_context) s
  let mapi ?hyp ?def s = S.update ~proof_context:(H.mapi ?hyp ?def s.proof_context) s

  let filter_map ?hyp ?def s = S.update ~proof_context:(H.filter_map ?hyp ?def s.proof_context) s

  let filter f s = S.update ~proof_context:(H.filter f s.proof_context) s

  (*------------------------------------------------------------------*)
  (* override [clear_triv] *)
  let clear_triv s =
    let not_triv = function
      | _, LHyp (Equiv.Local f) -> not (Term.f_triv f)
      | _ -> true
    in
    S.update ~proof_context:(H.filter not_triv s.proof_context) s

  let _pp ppe fmt s =
    let ppe = { ppe with table = s.env.table; } in
    H._pp ppe ~context:s.env.system fmt s.proof_context
      
  let pp     = _pp (default_ppe ~dbg:false ()) 
  let pp_dbg = _pp (default_ppe ~dbg:true  ()) 
end

(*------------------------------------------------------------------*)
let env     s = s.env
let vars    s = s.env.vars
let ty_vars s = s.env.ty_vars
let system  s = s.env.system
let table   s = s.env.table

let params s = Params.{ ty_vars = s.env.ty_vars; se_vars = s.env.se_vars; }

let set_env (env : Env.t) s = S.update ~env s

(*------------------------------------------------------------------*)
let set_vars (vars : Vars.env) s = 
  let env = Env.update ~vars s.env in
  S.update ~env s

let set_table table s = 
  let env = Env.update ~table s.env in
  S.update ~env s

(*------------------------------------------------------------------*)
let set_conclusion a s = S.update ~conclusion:a s 
let set_bound b s = S.update ?bound:b s

 (** See `.mli` *)
let set_conclusion_in_context ?update_local ?bound system conc s =
  if system = s.env.system && update_local = None then
    let s = set_conclusion conc s in set_bound bound s
  else

  (* Update hypotheses. *)
  let proof_context =
    change_trace_hyps_context
      ?update_local
      ~table:s.env.table
      ~old_context:s.env.system
      ~new_context:system
      ~vars:s.env.vars
      s.proof_context
  in
  (* Change the context in the sequent's environment. *)
  let env = Env.update ~system s.env in
  let s = S.update ~env ~proof_context ?bound s in

  (* Finally set the new conclusion. *)
  set_conclusion conc s

(** [pi proj s] returns the projection of [s] along [proj].
    Fails if [s.system.set] cannot be projected. *)
let pi projection s =
  let new_context =
    let context = s.env.system in
    let fset = SystemExpr.to_fset context.set in
    let new_set = SystemExpr.((project [projection] fset :> arbitrary)) in
    { context with set = new_set }
  in
  set_conclusion_in_context
    new_context
    (Term.project1 projection s.conclusion)
    s

(*------------------------------------------------------------------*)
let init ?(no_sanity_check = false) ~env ?bound conclusion =
  init_sequent ~no_sanity_check ~env ~bound ~conclusion

let conclusion s = s.conclusion
let bound s = s.bound

(*------------------------------------------------------------------*)
let subst subst s =
  if subst = [] then s else
    let proof_context = 
      H.map
        ~hyp:(Equiv.Any.subst subst)
        ~def:(fun (se,t) -> se, Term.subst subst t) 
        s.proof_context 
    in
    S.update
      ~proof_context
      ?bound:(omap (Term.subst subst) s.bound)
      ~conclusion:(Term.subst subst s.conclusion)
      s 

(*------------------------------------------------------------------*)
let gsubst (subst : Subst.t) s =
  if subst == Subst.empty_subst then s else
    let vars = Vars.map (fun v t -> Subst.subst_var subst v, t) s.env.vars in
    let proof_context = 
      H.map
        ~hyp:(Equiv.Any.gsubst subst)
        ~def:(fun (se,t) -> SE.gsubst subst se, Term.gsubst subst t) 
        s.proof_context
    in
    S.update
      ~env:(Env.update ~vars s.env)
      ~proof_context
      ?bound:(omap (Term.gsubst subst) s.bound)
      ~conclusion:(Term.gsubst subst s.conclusion)
      s 

(*------------------------------------------------------------------*)      
let rename (u:Vars.var) (v:Vars.var) (s:t) : t =
  assert (not (Vars.mem s.env.vars v));
  let s = subst [Term.ESubst (Term.mk_var u, Term.mk_var v)] s in
  let info = Vars.get_info u s.env.vars in
  S.update
    ~env:(Env.update
            ~vars:(Vars.add_var v info (Vars.rm_var u s.env.vars))
            s.env)
    s

(*------------------------------------------------------------------*)
(** TRS *)

let get_eqs_neqs (proof_context : H.hyps) =
  List.fold_left (fun (eqs, neqs) (atom : Term.Lit.xatom) -> match atom with
      | Comp (`Eq,  a, b) -> Term.ESubst (a,b) :: eqs, neqs
      | Comp (`Neq, a, b) -> eqs, Term.ESubst (a,b) :: neqs
      | _ -> assert false
    ) ([],[]) (get_eq_atoms proof_context)

let get_trs (s : sequent) = 
  let eqs,_ = get_eqs_neqs s.proof_context in
  Completion.complete s.env.table eqs

let eq_atoms_valid s =
  let trs = get_trs s in
  let () = dbg s.env.table "trs: %a" Completion.pp_state trs in

  let _, neqs = get_eqs_neqs s.proof_context in
  List.exists (fun (Term.ESubst (a, b)) ->
      if Completion.check_equalities trs [(a,b)] then
        let () =
          dbg s.env.table "dis-equality %a ≠ %a violated"
            Term.pp a Term.pp b
        in
        true
      else
        let () =
          dbg s.env.table "dis-equality %a ≠ %a: no violation"
            Term.pp a Term.pp b
        in
        false)
    neqs

(*------------------------------------------------------------------*)
let proof_context ?(in_system : SE.context option) (s : t) =
  let env =
    match in_system with
    | None -> s.env
    | Some system -> { s.env with system; }
  in
  ProofContext.make
    ~env
    ~hyps:(get_trace_hyps ~in_system:env.system s)

(*------------------------------------------------------------------*)
let mem_felem _ _ = false
let[@warning "-27"] change_felem ?loc _ _ _ = assert false
let[@warning "-27"] get_felem ?loc _ _ = assert false

(*------------------------------------------------------------------*)
module Conc = HighTerm.Smart
module Hyp  = Equiv.Any.Smart

(*------------------------------------------------------------------*)
type trace_sequent = t
