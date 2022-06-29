open Utils

module List = Utils.List

module SE = SystemExpr

module Args = TacticsArgs

(*------------------------------------------------------------------*)
type hyp_form = Equiv.any_form
type conc_form = Equiv.local_form

let hyp_kind = Equiv.Any_t
let conc_kind = Equiv.Local_t

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

    hint_db : Hint.hint_db;
    
    hyps : H.hyps;
    (** Hypotheses *)
    
    conclusion : Term.term;
    (** The conclusion / right-hand side formula of the sequent. *)    
  }

  val init_sequent :
    env:Env.t ->
    hint_db:Hint.hint_db ->
    conclusion:Term.term ->
    t

  val update :
    ?env:Env.t ->
    ?hyps:H.hyps ->
    ?conclusion:Term.term ->
    t -> t

end = struct
  type t = {
    env        : Env.t;
    hint_db    : Hint.hint_db;
    (* hind_db    : Reduction. *)
    hyps       : H.hyps;
    conclusion : Term.term;
  }

  let init_sequent ~env ~hint_db ~conclusion = {
    env ;
    hint_db;
    hyps = H.empty;
    conclusion;
  }

  let update ?env ?hyps ?conclusion t =
    let env        = Utils.odflt t.env env
    and hyps       = Utils.odflt t.hyps hyps
    and conclusion = Utils.odflt t.conclusion conclusion in
    { t with env; hyps; conclusion; } 
end

include S

type sequent = S.t
type sequents = sequent list

let pp ppf s =
  let open Fmt in
  pf ppf "@[<v 0>" ;
  pf ppf "@[System: %a@]@;"
    SystemExpr.pp_context s.env.system;

  if s.env.ty_vars <> [] then
    pf ppf "@[Type variables: %a@]@;" 
      (Fmt.list ~sep:Fmt.comma Type.pp_tvar) s.env.ty_vars ;

  if s.env.vars <> Vars.empty_env then
    pf ppf "@[Variables: %a@]@;" Vars.pp_env s.env.vars ;

  (* Print hypotheses *)
  H.pp ppf s.hyps ;

  (* Print separation between hyps and conclusion *)
  Printer.kws `Separation ppf (String.make 40 '-') ;
  (* Print conclusion formula and close box. *)
  pf ppf "@;%a@]" Term.pp s.conclusion

(*------------------------------------------------------------------*)
let get_all_messages (s : sequent) =
  let atoms = Hyps.get_message_atoms s.hyps in
  let atoms =
    match Term.form_to_xatom s.conclusion with
      | Some at -> at :: atoms
      | _ -> atoms
  in
  List.fold_left (fun acc at -> match at with
      | `Happens _ -> acc
      | (`Comp (_,a,b)) -> a :: b :: acc
    ) [] atoms

(*------------------------------------------------------------------*)
(** Prepare constraints or TRS query *)

let _get_models (hyps : H.hyps) =
  let hyps = H.fold (fun _ f acc ->
      match f with
      | Local f
      | Global Equiv.(Atom (Reach f)) -> f :: acc
      | Global _ -> acc
    ) hyps [] 
  in
  Constr.models_conjunct hyps

let get_models (s : sequent) = _get_models s.hyps

let query ~precise s q =
  let models = get_models s in
  Constr.query ~precise models q

let query_happens ~precise s a = query ~precise s [`Pos, `Happens a]

let maximal_elems ~precise s tss =
  let models = get_models s in
  Constr.maximal_elems ~precise models tss

let get_ts_equalities ~precise s =
  let models = get_models s in
  let ts = List.map (fun (_,x) -> x) (Hyps.get_trace_literals s.hyps)
             |>  Atom.trace_atoms_ts in
  Constr.get_ts_equalities ~precise models ts

let get_ind_equalities ~precise s =
  let models = get_models s in
  let inds = List.map (fun (_,x) -> x) (Hyps.get_trace_literals s.hyps)
             |> Atom.trace_atoms_ind in
  Constr.get_ind_equalities ~precise models inds

let constraints_valid s =
  let models = get_models s in
  not (Constr.m_is_sat models)

(*------------------------------------------------------------------*)  
module AnyHyps
  : Hyps.S1 with type hyp = Equiv.any_form and type hyps := t
= struct

  type sequent = t

  type hyp = Equiv.any_form

  type ldecl = Ident.t * hyp
    
  let pp_hyp = Equiv.pp_any_form
  let pp_ldecl = H.pp_ldecl

  let fresh_id  ?approx name  s = H.fresh_id  ?approx name  s.hyps
  let fresh_ids ?approx names s = H.fresh_ids ?approx names s.hyps

  let is_hyp f s = H.is_hyp f s.hyps

  let by_id   id s = H.by_id   id s.hyps
  let by_name id s = H.by_name id s.hyps

  let to_list s = H.to_list s.hyps

  let mem_id   id s = H.mem_id   id s.hyps
  let mem_name id s = H.mem_name id s.hyps

  let find_opt func s = H.find_opt func s.hyps

  let find_map func s = H.find_map func s.hyps

  let find_all func s = H.find_all func s.hyps
      
  let exists func s = H.exists func s.hyps

  let _add ~(force:bool) id hyp s =
    let id, hyps = H._add ~force id hyp s.hyps in
    id, S.update ~hyps s

  let add_i npat f s =
    let id, hyps = H.add_i npat f s.hyps in
    id, S.update ~hyps s

  let add npat f s = S.update ~hyps:H.(add npat f s.hyps) s

  let add_i_list l (s : sequent) =
    let ids, hyps = H.add_i_list l s.hyps in
    ids, S.update ~hyps s

  let add_list l s = snd (add_i_list l s)
  
  let remove id s = S.update ~hyps:(H.remove id s.hyps) s

  let fold func s init = H.fold func s.hyps init

  let map f s  = S.update ~hyps:(H.map f s.hyps)  s
  let mapi f s = S.update ~hyps:(H.mapi f s.hyps) s

  let filter f s = S.update ~hyps:(H.filter f s.hyps) s

  (*------------------------------------------------------------------*)
  (* override [clear_triv] *)
  let clear_triv s =
    let not_triv _ = function
      | Equiv.Local f -> not (Term.f_triv f)
      | _ -> true
    in
    S.update ~hyps:(H.filter not_triv s.hyps) s

  let pp     fmt s = H.pp     fmt s.hyps
  let pp_dbg fmt s = H.pp_dbg fmt s.hyps
end

(*------------------------------------------------------------------*)
let env     s = s.env
let vars    s = s.env.vars
let ty_vars s = s.env.ty_vars
let system  s = s.env.system
let table   s = s.env.table

let set_env env s = S.update ~env s

let set_vars (vars : Vars.env) s = 
  let env = Env.update ~vars s.env in
  S.update ~env s

let set_table table s = 
  let env = Env.update ~table s.env in
  S.update ~env s

(*------------------------------------------------------------------*)

(** Add to [s] equalities corresponding to the expansions of all macros
  * occurring in [f], if [f] happened. *)
let rec add_macro_defs (s : sequent) f =
  let macro_eqs : (Term.term * Term.term) list ref = ref [] in
  match SystemExpr.to_fset s.env.system.set with
  | exception _ -> s
  | system ->

    List.fold_left (fun s (a,f) -> 
        if query_happens ~precise:true s a 
        then snd (add_form_aux None s f)
        else s
      ) s !macro_eqs

and add_form_aux
    ?(force=false) (id : Ident.t option) (s : sequent) (f : Term.term) =
  let recurse =
    (not (H.is_hyp (Local f) s.hyps)) && (Config.auto_intro ()) in

  let id = match id with       
    | None -> H.fresh_id "D" s.hyps
    | Some id -> id in

  let id, hyps = H._add ~force id (Local f) s.hyps in
  let s = S.update ~hyps s in

  (* [recurse] boolean to avoid looping *)
  let s = if recurse then add_macro_defs s f else s in

  id, s

let set_goal a s =
  let s = S.update ~conclusion:a s in
    match Term.form_to_xatom a with
      | Some at 
        when Term.ty_xatom at = Type.Message && 
             Config.auto_intro () -> 
        add_macro_defs s a
      | _ -> s

let set_goal_in_context ?update_local system conc s =

  if system = s.env.system && update_local = None then
    set_goal conc s
  else

  (* Update hypotheses.
     We add back manually all formulas, to ensure that definitions are
     unrolled. TODO really necessary? *)
  let default_update_local,update_global =
    LowSequent.setup_set_goal_in_context
      ~table:s.env.table
      ~old_context:s.env.system
      ~new_context:system
  in
  let update_local = match update_local with
    | None -> default_update_local
    | Some f -> f
  in
  let s =
    H.fold
      (fun id f s ->
         match f with
           | Local f ->
               begin match update_local f with
                 | Some f ->
                   let _,hyps = H._add ~force:true id (Local f) s.hyps in
                   S.update ~hyps s
                 | None -> s
               end
           | Global e ->
               begin match update_global e with
                 | Some e ->
                     let _,hyps = H._add ~force:true id (Global e) s.hyps in
                     S.update ~hyps s
                 | None -> s
               end)
      s.hyps (S.update ~hyps:H.empty s)
  in

  (* Change the context in the sequent's environment. *)
  let env = Env.update ~system s.env in
  let s = S.update ~env s in

  (* Finally set the new conclusion. *)
  set_goal conc s

(** [pi proj s] returns the projection of [s] along [proj].
    Fails if [s.system.set] cannot be projected. *)
let pi projection s =
  let new_context =
    let context = s.env.system in
    let fset = SystemExpr.to_fset context.set in
    let new_set = SystemExpr.((project [projection] fset :> arbitrary)) in
    { context with set = new_set }
  in
  set_goal_in_context
    new_context
    (Term.project1 projection s.conclusion)
    s

let init ~env ~hint_db conclusion =
  init_sequent ~env ~hint_db ~conclusion

let goal s = s.conclusion

(*------------------------------------------------------------------*)
let subst subst s =
  if subst = [] then s else
    let hyps = H.map (Equiv.Any.subst subst) s.hyps in
    let s =
      S.update
        ~hyps:hyps
        ~conclusion:(Term.subst subst s.conclusion)
        s in

    s

let rename (u:Vars.var) (v:Vars.var) (s:t) : t =
  assert (not (Vars.mem s.env.vars v));
  let s = subst [Term.ESubst (Term.mk_var u, Term.mk_var v)] s in
  S.update
    ~env:(Env.update
            ~vars:(Vars.add_var v (Vars.rm_var u s.env.vars))
            s.env)
    s


(*------------------------------------------------------------------*)
(** TRS *)

let get_eqs_neqs s =
  List.fold_left (fun (eqs, neqs) (atom : Term.xatom) -> match atom with
      | `Comp (`Eq,  a, b) -> Term.ESubst (a,b) :: eqs, neqs
      | `Comp (`Neq, a, b) -> eqs, Term.ESubst (a,b) :: neqs
      | _ -> assert false
    ) ([],[]) (Hyps.get_eq_atoms s)

let get_trs s = 
  let eqs,_ = get_eqs_neqs s.hyps in
  Completion.complete s.env.table eqs

let eq_atoms_valid s =
  let trs = get_trs s in
  let () = dbg "trs: %a" Completion.pp_state trs in

  let _, neqs = get_eqs_neqs s.hyps in
  List.exists (fun (Term.ESubst (a, b)) ->
      if Completion.check_equalities trs [(a,b)] then
        let () = dbg "dis-equality %a ≠ %a violated" Term.pp a Term.pp b in
        true
      else
        let () = dbg "dis-equality %a ≠ %a: no violation"
            Term.pp a Term.pp b in
        false)
    neqs

let literals_unsat_smt ?(slow=false) s =
  Smt.literals_unsat ~slow
    s.env.table
    (SystemExpr.to_fset s.env.system.set) (* TODO handle failure *)
    (Vars.to_list s.env.vars)
    (Hyps.get_message_atoms s.hyps)
    (Hyps.get_trace_literals s.hyps)
    (* TODO: now that we can pass more general formulas than lists of atoms,
     * we don't actually need to decompose message atoms / trace literals *)
    (* since we didn't move the conclusion into the premises,
     * handle it here *)
    (Term.mk_not s.conclusion :: Hint.get_smt_db s.hint_db)


(*------------------------------------------------------------------*)
let mk_trace_cntxt ?se s =
  let system = odflt (SE.to_fset s.env.system.set) se in
  Constr.{
    table  = table s;
    system;
    models = Some (get_models s);
  }

(*------------------------------------------------------------------*)
let hint_db s = s.hint_db

(*------------------------------------------------------------------*)
let get_trace_hyps s = s.hyps

(*------------------------------------------------------------------*)
let mem_felem _ _ = false
let change_felem ?loc _ _ _ = assert false
let get_felem ?loc _ _ = assert false

(*------------------------------------------------------------------*)
let map f s : sequent =
  let f' x = f.Equiv.Babel.call Equiv.Any_t x in
  set_goal (f.Equiv.Babel.call Equiv.Local_t (goal s)) (AnyHyps.map f' s)

(*------------------------------------------------------------------*)
let fv s : Vars.Sv.t = 
  let h_vars = 
    AnyHyps.fold (fun _ f vars -> 
        Vars.Sv.union (Equiv.Any.fv f) vars
      ) s Vars.Sv.empty
  in
  Vars.Sv.union h_vars (Term.fv (goal s))

(*------------------------------------------------------------------*)
module Conc = Term.Smart
module Hyp  = Equiv.Any.Smart

(*------------------------------------------------------------------*)
type trace_sequent = t

module LocalHyps
  : Hyps.S1 with type hyp = Equiv.local_form and type hyps := trace_sequent
= struct
  type hyp = Equiv.local_form
  type ldecl = Ident.t * hyp
    
  let (!!) = function
    | Equiv.Local h -> h
    | Equiv.Global _ -> assert false

  let _add ~force p h s = AnyHyps._add ~force p (Local h) s
      
  let add p h s = AnyHyps.add p (Local h) s

  let add_i p h s = AnyHyps.add_i p (Local h) s

  let add_i_list l s =
    let l = List.map (fun (p,h) -> p, Equiv.Local h) l in
    AnyHyps.add_i_list l s

  let add_list l s = snd (add_i_list l s)

  let pp_hyp = Term.pp

  let pp_ldecl ?dbg fmt (id,h) = AnyHyps.pp_ldecl ?dbg fmt (id,Local h)

  let fresh_id = AnyHyps.fresh_id
  let fresh_ids = AnyHyps.fresh_ids

  let is_hyp h s = AnyHyps.is_hyp (Local h) s

  let by_id id s = !!(AnyHyps.by_id id s)

  let by_name name s =
    let l,h = AnyHyps.by_name name s in
    l,!!h

  let mem_id = AnyHyps.mem_id

  let mem_name = AnyHyps.mem_name
  let to_list s =
    List.filter_map
      (function
         | l, Equiv.Local h -> Some (l,h)
         | l, Equiv.Global _ -> None)
      (AnyHyps.to_list s)

  let find_opt f s =
    let f id = function
      | Equiv.Local h -> f id h
      | Equiv.Global _ -> false
    in
    match AnyHyps.find_opt f s with
      | None -> None
      | Some (id,Local h) -> Some (id,h)
      | _ -> assert false

  let find_map f s =
    let f id = function
      | Equiv.Local h -> f id h
      | Equiv.Global _ -> None
    in
    AnyHyps.find_map f s

  let find_all f s =
    let f id = function
      | Equiv.Local h -> f id h
      | Equiv.Global _ -> false
    in
    List.map (fun (id, h) -> id, Equiv.any_to_reach h) (AnyHyps.find_all f s)
      
  let exists f s =
    let f id = function
      | Equiv.Local h -> f id h
      | Equiv.Global _ -> false
    in
    AnyHyps.exists f s

  let map f s =
    let f = function
      | Equiv.Global h -> Equiv.Global h
      | Equiv.Local h  -> Equiv.Local (f h)
    in
    AnyHyps.map f s

  let mapi f s =
    let f i = function
      | Equiv.Global h -> Equiv.Global h
      | Equiv.Local h  -> Equiv.Local (f i h)
    in
    AnyHyps.mapi f s

  let filter f s =
    let f i = function Equiv.Global h -> true | Equiv.Local h -> f i h in
    AnyHyps.filter f s
    
  let remove = AnyHyps.remove

  let fold f s =
    let f id h acc = match h with
      | Equiv.Global _ -> acc
      | Equiv.Local  h -> f id h acc
    in
    AnyHyps.fold f s

  let clear_triv = AnyHyps.clear_triv

  let pp = AnyHyps.pp
  let pp_dbg = AnyHyps.pp_dbg
end

(*------------------------------------------------------------------*)
module Hyps
  : Hyps.S1 with type hyp = Equiv.any_form and type hyps := t
= AnyHyps
