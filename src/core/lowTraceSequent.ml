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
let dbg ?(force=false) s =
  let mode = if Config.debug_tactics () || force then `Dbg else `Ignore in
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

  let fv (s : t) : Vars.Sv.t = 
    let h_vars = 
      H.fold (fun _ ld vars -> 
          match ld with
          | LHyp f     -> Vars.Sv.union (Equiv.Any.fv f) vars
          | LDef (_,t) -> Vars.Sv.union (Term.fv      t) vars
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
        Fmt.epr "Anomaly in LowTraceSequent.sanity_check:@.%a@.@.
                 Fail on %a @.not in %a @.@."
          pp_dbg s
          (Fmt.list Vars.pp) (Vars.Sv.elements (fv s))
          (Fmt.list Vars.pp) (Vars.Sv.elements (Vars.to_vars_set s.env.Env.vars))
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
let get_all_messages (s : sequent) =
  let atoms = List.map snd (Hyps.get_atoms_of_hyps s.proof_context) in
  (*TODO:Concrete : Probably something to here but not sure for now*)
  let atoms =
    match Term.Lit.form_to_xatom s.conclusion with
      | Some at -> at :: atoms
      | _ -> atoms
  in
  List.fold_left (fun acc at ->
      match at with
      | Term.Lit.Happens _ -> acc
      | Term.Lit.Comp (_,a,b) -> a :: b :: acc
      | Term.Lit.Atom a -> a :: acc
    ) [] atoms

(*------------------------------------------------------------------*)
(** Prepare constraints or TRS query *)

let get_models table (proof_context : H.hyps) =
  let proof_context = 
    H.fold (fun _ f acc ->
        match f with
        | LHyp (Local f)
        | LHyp (Global Equiv.(Atom (Reach {formula = f;bound = _}))) -> f :: acc
        (*TODO:Concrete : Make sure it is right*)
        | LHyp (Global _) -> acc
        | LDef (_se, _t) -> acc
        (* FIXME: we cannot translate definitions, as doing so
           requires checking in which system `id` appears, which is
           not easy (this will be possible once macros are decorated
           with the system used to interpret them) *)
      ) proof_context [] 
  in
  Constr.models_conjunct
    ~timeout:(TConfig.solver_timeout table)
    ~table
    proof_context

let get_models (s : sequent) = get_models s.env.table s.proof_context

(*------------------------------------------------------------------*)
(** General version of query, which subsumes the functions
    constraints_valid and query that will eventually be exported,
    and provides joint benchmarking support. *)

let query ~precise s = function
  | None -> not (Constr.m_is_sat (get_models s))
  | Some q -> Constr.query ~precise (get_models s) q

module ConstrBenchmark = Benchmark.Make(struct
  type input = bool * sequent * Term.Lit.literals option
  type output = bool
  let default =
    "Constr",
    (fun (precise,s,q) -> query ~precise s q)
  let basename = "squirrel_bench_constr_"
  let pp_input ch (_,_,q) = match q with
    | None -> Format.fprintf ch "false"
    | Some q -> Term.Lit.pps ch q
  let pp_result ch = function
    | Ok b -> Format.fprintf ch "%b" b
    | Error _ -> Format.fprintf ch "fail"
end)

let register_query_alternative name alt =
  ConstrBenchmark.register_alternative
    name
    (fun (precise,s,q) -> alt ~precise s q)

let query ~precise s q =
  ConstrBenchmark.run (precise,s,q)

(** Exported versions of query and its alternatives. *)

let query_happens ~precise s a =
  query ~precise s (Some [`Pos, Happens a])

let constraints_valid s =
  (* The precise flag is irrelevant in that case. *)
  query ~precise:true s None

let query ~precise s q =
   query ~precise s (Some q)

(** Other uses of Constr *)

let maximal_elems ~precise s tss =
  let models = get_models s in
  Constr.maximal_elems ~precise models tss

let get_ts_equalities ~precise s =
  let models = get_models s in
  let ts = List.map (fun (_,x) -> x) (Hyps.get_trace_literals s.proof_context)
             |>  Atom.trace_atoms_ts in
  Constr.get_ts_equalities ~precise models ts

(** Variant of [get_models] with separate profiling to track
    uses other than those above.
    Note that [get_models] relies on [Constr.models_conjunct]
    which is independently profiled.
    We do not profile [maximal_elems] and [get_ts_equalities]
    although they do use [get_models],
    but the underlying functions in [Constr] are profiled. *)
let get_models = Prof.mk_unary "TS.get_models" get_models

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
let tsubst (tsubst : Type.tsubst) s =
  if tsubst == Type.tsubst_empty then s else
    let vars = Vars.map (fun v t -> Vars.tsubst tsubst v, t) s.env.vars in
    let proof_context = 
      H.map
        ~hyp:(Equiv.Any.tsubst tsubst)
        ~def:(fun (se,t) -> se, Term.tsubst tsubst t) 
        s.proof_context
    in
    S.update
      ~env:(Env.update ~vars s.env)
      ~proof_context
      ?bound:(omap (Term.tsubst tsubst) s.bound)
      ~conclusion:(Term.tsubst tsubst s.conclusion)
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
  let () = dbg "trs: %a" Completion.pp_state trs in

  let _, neqs = get_eqs_neqs s.proof_context in
  List.exists (fun (Term.ESubst (a, b)) ->
      if Completion.check_equalities trs [(a,b)] then
        let () = dbg "dis-equality %a ≠ %a violated" Term.pp a Term.pp b in
        true
      else
        let () = dbg "dis-equality %a ≠ %a: no violation"
            Term.pp a Term.pp b in
        false)
    neqs

(*------------------------------------------------------------------*)
let mk_trace_cntxt ?se s =
  let system = odflt (SE.to_fset s.env.system.set) se in
  Constr.{
    table  = table s;
    system;
    models = Some (get_models s);
  }

(*------------------------------------------------------------------*)
let get_trace_hyps s = s.proof_context

(*------------------------------------------------------------------*)
let mem_felem _ _ = false
let[@warning "-27"] change_felem ?loc _ _ _ = assert false
let[@warning "-27"] get_felem ?loc _ _ = assert false

(*------------------------------------------------------------------*)
module Conc = HighTerm.Smart
module Hyp  = Equiv.Any.Smart

(*------------------------------------------------------------------*)
type trace_sequent = t
