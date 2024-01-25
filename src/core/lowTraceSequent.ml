open Utils

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
    
    conclusion : Term.term;
    (** The conclusion / right-hand side formula of the sequent. *)    
  }

  val pp     :             Format.formatter -> t -> unit
  val _pp    : dbg:bool -> Format.formatter -> t -> unit
  val pp_dbg :             Format.formatter -> t -> unit

  val init_sequent :
    no_sanity_check:bool ->
    env:Env.t ->
    conclusion:Term.term ->
    t

  val fv : t -> Vars.Sv.t

  val sanity_check : t -> unit
                     
  val update :
    ?env:Env.t ->
    ?proof_context:H.hyps ->
    ?conclusion:Term.term ->
    t -> t

end = struct
  type t = {
    env           : Env.t;
    proof_context : H.hyps;
    conclusion    : Term.term;
  }
  
  let _pp ~dbg ppf s =
    let env_without_defined_vars = 
      H.fold (fun id ld env ->
          match ld with
          | LDef (_,t) -> Vars.rm_var (Vars.mk id (Term.ty t)) env
          | _ -> env
        ) s.proof_context s.env.vars
    in
    Fmt.pf ppf "@[<v 0>" ;
    Fmt.pf ppf "@[System: %a@]@;"
      SystemExpr.pp_context s.env.system;

    if s.env.ty_vars <> [] then
      Fmt.pf ppf "@[Type variables: %a@]@;" 
        (Fmt.list ~sep:Fmt.comma Type.pp_tvar) s.env.ty_vars ;

    if s.env.vars <> Vars.empty_env then
      Fmt.pf ppf "@[<hv 2>Variables:@ @[%a@]@]@;"
        (Vars._pp_env ~dbg) env_without_defined_vars ;

    (* Print hypotheses *)
    H._pp ~dbg ~context:s.env.system ppf s.proof_context ;

    (* Print separation between proof_context and conclusion *)
    Printer.kws `Separation ppf (String.make 40 '-') ;
    (* Print conclusion formula and close box. *)
    Fmt.pf ppf "@;%a@]" (Term._pp ~dbg) s.conclusion

  let pp     = _pp ~dbg:false
  let pp_dbg = _pp ~dbg:true

  let fv (s : t) : Vars.Sv.t = 
    let h_vars = 
      H.fold (fun _ ld vars -> 
          match ld with
          | LHyp f     -> Vars.Sv.union (Equiv.Any.fv f) vars
          | LDef (_,t) -> Vars.Sv.union (Term.fv      t) vars
        ) s.proof_context Vars.Sv.empty
    in
    Vars.Sv.union h_vars (Term.fv s.conclusion)

  let ty_fv (s : t) : Type.Fv.t =
    let h_vars =
      H.fold (fun _ ld vars ->
          match ld with
          | LHyp f     -> Type.Fv.union (Equiv.Any.ty_fv f) vars
          | LDef (_,t) -> Type.Fv.union (Term.ty_fv      t) vars
        ) s.proof_context Type.Fv.empty
    in
    Type.Fv.union h_vars (Term.ty_fv s.conclusion)

  let sanity_check s : unit =
    Vars.sanity_check s.env.Env.vars;

    if not (Vars.Sv.subset (fv s) (Vars.to_vars_set s.env.Env.vars)) then
      let () =
        Fmt.epr "Anomaly in LowTraceSequent.sanity_check:@.%a@.@." pp_dbg s
      in
      assert false
    else ();

    let tyfv = ty_fv s in
    (* all type variables are bound *)
    assert (Sid.subset tyfv.tv
              (Sid.of_list (List.map Type.ident_of_tvar s.env.ty_vars)));
    (* no univars remaining *)
    assert (Sid.subset tyfv.uv Sid.empty)


  let init_sequent ~no_sanity_check ~(env : Env.t) ~conclusion =
    let proof_context = H.empty in
    let s = { env ; proof_context; conclusion; } in
    if not no_sanity_check then sanity_check s;
    s

  let update ?env ?proof_context ?conclusion t =
    let env           = Utils.odflt t.env env
    and proof_context = Utils.odflt t.proof_context proof_context
    and conclusion    = Utils.odflt t.conclusion conclusion in
    { env; proof_context; conclusion; } 
end

include S

type sequent = S.t
type sequents = sequent list

(*------------------------------------------------------------------*)
let get_all_messages (s : sequent) =
  let atoms = List.map snd (Hyps.get_atoms_of_hyps s.proof_context) in
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
    H.fold_hyps (fun _ f acc ->
        match f with
        | Local f
        | Global Equiv.(Atom (Reach f)) -> f :: acc
        | Global _ -> acc
      ) proof_context [] 
  in
  Constr.models_conjunct (TConfig.solver_timeout table) proof_context

let get_models (s : sequent) = get_models s.env.table s.proof_context

(*------------------------------------------------------------------*)
(** General version of query, which subsumes the functions
    constraints_valid and query that will eventually be exported,
    and provides joint benchmarking support. *)

let query ~precise s = function
  | None -> not (Constr.m_is_sat (get_models s))
  | Some q -> Constr.query ~precise (get_models s) q

module Benchmark = struct

  let query_methods = ref ["Constr",query]
  let register_query_alternative name f =
    query_methods := !query_methods @ [name,f]
  let query_id = ref 0
  let query_pos = ref ""
  let set_position pos = query_pos := pos
  let log_chan =
    Lazy.from_fun (fun () ->
      match Sys.getenv_opt "BENCHMARK_DIR" with
      | None -> None
      | Some temp_dir ->
        let fname = Filename.temp_file ~temp_dir "squirrel_bench_" ".txt" in
        Some (Format.formatter_of_out_channel (open_out fname)))
  let pp_result ch = function
    | Error _ -> Format.fprintf ch "failure"
    | Ok b -> Format.fprintf ch "%b" b
  let log (name,query,result,time) =
    match Lazy.force log_chan with
    | None -> ()
    | Some ch ->
      let query =
        match query with
        | None -> "false"
        | Some q -> Format.asprintf "%a" Term.Lit.pps q
      in
      Format.fprintf ch
        "%d:%s:%s:%S:%a:%f@."
        !query_id
        !query_pos
        name
        query
        pp_result result
        time
  let get_result ~precise s q (name,f) =
    let t0 = Unix.gettimeofday () in
    match f ~precise s q with
    | r -> name, q, Ok r, Unix.gettimeofday () -. t0
    | exception e -> name, q, Error e, Unix.gettimeofday () -. t0
end

let query ~precise s q =
  let open Benchmark in
  incr Benchmark.query_id;
  let results = List.map (get_result ~precise s q) !query_methods in
  List.iter log results;
  match List.hd results with
  | _,_,Error e,_ -> raise e
  | _,_,Ok r,_ -> r

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
  let pp_ldecl = H.pp_ldecl

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

  let pp          fmt s = H.pp                                fmt s.proof_context
  let _pp    ~dbg fmt s = H._pp    ~dbg ~context:s.env.system fmt s.proof_context
  let pp_dbg      fmt s = H.pp_dbg                            fmt s.proof_context
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

(** See `.mli` *)
let set_conclusion_in_context ?update_local system conc s =
  if system = s.env.system && update_local = None then
    set_conclusion conc s
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
  let s = S.update ~env ~proof_context s in

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
let init ?(no_sanity_check = false) ~env conclusion =
  init_sequent ~no_sanity_check ~env ~conclusion

let conclusion s = s.conclusion

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
