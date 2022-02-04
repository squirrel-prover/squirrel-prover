module List = Utils.List

module Args = TacticsArgs

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
let get_ord (at : Term.xatom ) : Term.ord = match at with
  | `Comp (ord,_,_) -> ord
  | `Happens _      -> assert false

(** Chooses a name for a formula, depending on an old name (if any), and the
    formula shape. *)
let choose_name = function
  | `Equiv _ -> "G"
  | `Reach f ->
    match Term.form_to_xatom f with
    | None -> "H"
    | Some (`Happens _) -> "Hap"
    | Some at ->
      let sort = match Term.ty_xatom at with
        | Type.Timestamp -> "C"
        | Type.Index     -> "I"
        | _              -> "M" 
      in
      let ord = match get_ord at with
        | `Eq  -> "eq"
        | `Neq -> "neq"
        | `Leq -> "le"
        | `Geq -> "ge"
        | `Lt  -> "lt"
        | `Gt  -> "gt"
      in
    sort ^ ord

(*------------------------------------------------------------------*)
module FHyp = struct
  type t = hyp_form
  let pp_hyp = Equiv.Any.pp
  let htrue = `Reach Term.mk_true
end

module H = Hyps.Mk(FHyp)

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
    SystemExpr.pp s.env.system;

  if s.env.ty_vars <> [] then
    pf ppf "@[Type variables: %a@]@;" 
      (Fmt.list ~sep:Fmt.comma Type.pp_tvar) s.env.ty_vars ;

  if s.env.vars <> Vars.empty_env then
    pf ppf "@[Variables: %a@]@;" Vars.pp_env s.env.vars ;

  (* Print hypotheses *)
  H.pps ppf s.hyps ;

  (* Print separation between hyps and conclusion *)
  Printer.kws `Separation ppf (String.make 40 '-') ;
  (* Print conclusion formula and close box. *)
  pf ppf "@;%a@]" Term.pp s.conclusion


(*------------------------------------------------------------------*)
(** Collect specific local hypotheses *)
  
let get_atoms_of_fhyps (forms : FHyp.t list) : Term.literals =
  List.fold_left (fun acc f ->
      match f with
      | `Equiv _ -> acc
      | `Reach f ->
        match Term.form_to_literals f with
        | `Entails lits | `Equiv lits -> lits @ acc
    ) [] forms 

let get_atoms_from_s (s : sequent) : Term.literals =
  let fhyps = H.fold (fun _ f acc -> f :: acc) s.hyps [] in
  get_atoms_of_fhyps fhyps

let get_message_atoms (s : sequent) : Term.xatom list =
  let do1 (at : Term.literal) : Term.xatom option =
    match Term.ty_lit at with
    | Type.Timestamp | Type.Index -> None
    | _ ->
      (* FIXME: move simplifications elsewhere *)
      match at with 
      | `Pos, (`Comp _ as at)       -> Some at
      | `Neg, (`Comp (`Eq, t1, t2)) -> Some (`Comp (`Neq, t1, t2))
      | _ -> None
  in
  List.filter_map do1 (get_atoms_from_s s)

let get_trace_literals (s : sequent) : Term.literals =
  let do1 (lit : Term.literal) : Term.literal option =
    match Term.ty_lit lit with 
    | Type.Index | Type.Timestamp -> Some lit
    | _ -> None
  in
  List.filter_map do1 (get_atoms_from_s s)

let get_eq_atoms (s : sequent) : Term.xatom list =
  let do1 (lit : Term.literal) : Term.xatom option =
    match lit with 
    | `Pos, (`Comp ((`Eq | `Neq), _, _) as at) -> Some at

    | `Neg, (`Comp (`Eq,  t1, t2)) -> Some (`Comp (`Neq, t1, t2))
    | `Neg, (`Comp (`Neq, t1, t2)) -> Some (`Comp (`Eq,  t1, t2))

    | _ -> None
  in
  List.filter_map do1 (get_atoms_from_s s)

let get_all_messages s =
  let atoms = get_message_atoms s in
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

let get_models_t s : Constr.models Utils.timeout_r =
  let trace_literals = get_trace_literals s in
  Constr.models_conjunct trace_literals 

let get_models s = Tactics.timeout_get (get_models_t s)

let query ~precise s q =
  let models = get_models s in
  Constr.query ~precise models q

let query_happens ~precise s a = query ~precise s [`Pos, `Happens a]

let maximal_elems ~precise s tss =
  let models = get_models s in
  Constr.maximal_elems ~precise models tss

let get_ts_equalities ~precise s =
  let models = get_models s in
    let ts = List.map (fun (_,x) -> x) (get_trace_literals s)
             |>  Atom.trace_atoms_ts in
    Constr.get_ts_equalities ~precise models ts

let get_ind_equalities ~precise s =
  let models = get_models s in
  let inds = List.map (fun (_,x) -> x) (get_trace_literals s)
             |> Atom.trace_atoms_ind in
  Constr.get_ind_equalities ~precise models inds

let constraints_valid s =
  let models = get_models s in
  not (Constr.m_is_sat models)

(*------------------------------------------------------------------*)  
module Hyps = struct

  type sequent = t

  type hyp = Equiv.any_form

  type ldecl = Ident.t * hyp

  let pp_hyp = Term.pp 
  let pp_ldecl = H.pp_ldecl

  let fresh_id ?(approx=false) name s =
    let id = H.fresh_id name s.hyps in
    if (not approx) && Ident.name id <> name && name <> "_"
    then Tactics.soft_failure (Tactics.HypAlreadyExists name)
    else id

  let fresh_ids ?(approx=false) names s =
    let ids = H.fresh_ids names s.hyps in
    
    if approx then ids else
      begin
        List.iter2 (fun id name ->
            if Ident.name id <> name && name <> "_"
            then Tactics.soft_failure (Tactics.HypAlreadyExists name)
          ) ids names;
        ids
      end

  let is_hyp f s = H.is_hyp f s.hyps

  let by_id   id s = H.by_id   id s.hyps
  let by_name id s = H.by_name id s.hyps

  let to_list s = H.to_list s.hyps

  let mem_id   id s = H.mem_id   id s.hyps
  let mem_name id s = H.mem_name id s.hyps

  let find_opt func s = H.find_opt func s.hyps

  let find_map func s = H.find_map func s.hyps
      
  let exists func s = H.exists func s.hyps

  class iter_macros ~cntxt f = object (self)
    inherit Iter.iter ~cntxt as super
    method visit_message t =
      match t with
      | Term.Macro (ms,[],a) ->
        if List.for_all
            Vars.(fun v -> not (is_new v))
            (Term.get_vars t) 
        then begin
          match Macros.get_definition cntxt ms a with
          | `Def def ->
            f a (`Message (t, def)) ;
            self#visit_message def
          | _ -> ()
        end

      | t -> super#visit_message t
  end

  (** Add to [s] equalities corresponding to the expansions of all macros
    * occurring in [f], if [f] happened. *)
  let rec add_macro_defs (s : sequent) f =
    let macro_eqs : (Term.term * Term.term) list ref = ref [] in
    let cntxt = Constr.{ 
        table = s.env.table;
        system = s.env.system;
        models = None;
      } in
        
    let iter =
      new iter_macros
        ~cntxt
        (fun a el -> match el with
           |`Message (t,t') ->
             if Term.ty t <> Type.Boolean then
               macro_eqs := (a, Term.mk_atom `Eq t t') :: !macro_eqs
        ) in
    
    iter#visit_message f ;
    
    List.fold_left (fun s (a,f) -> 
        if query_happens ~precise:true s a 
        then snd (add_form_aux None s f)
        else s
      ) s !macro_eqs

  and add_form_aux
      ?(force=false) (id : Ident.t option) (s : sequent) (f : Term.term) =
    let recurse =
      (not (H.is_hyp (`Reach f) s.hyps)) && (Config.auto_intro ()) in

    let id = match id with       
      | None -> H.fresh_id "D" s.hyps
      | Some id -> id in

    let id, hyps = H.add ~force id (`Reach f) s.hyps in
    let s = S.update ~hyps s in
    
    (* [recurse] boolean to avoid looping *)
    let s = if recurse then add_macro_defs s f else s in

    id, s

  let add_happens ?(force=false) id (s : sequent) ts =
    let f = Term.mk_happens ts in
    let id, hyps = H.add ~force id (`Reach f) s.hyps in
    let s = S.update ~hyps s in
    id, s

  (** if [force], we add the formula to [Hyps] even if it already exists. *)
  let add_formula ?(force=false) id f (s : sequent) =
    match f with
    | Term.Fun (f, _, [ts]) when f = Term.f_happens -> 
      add_happens ~force id s ts

    | _ -> add_form_aux ~force (Some id) s f

  let add_i npat f s =
    let force, approx, name = match npat with
      | Args.Unnamed  -> true, true, "_"
      | Args.AnyName  -> false, true, choose_name f
      | Args.Named s  -> true, false, s 
      | Args.Approx s -> true, true, s 
    in
    let id = fresh_id ~approx name s in
    match f with
      | `Reach f -> add_formula ~force id f s
      | _ ->
         let id,hyps = H.add ~force id f s.hyps in
         id, S.update ~hyps s

  let add npat f s = snd (add_i npat f s)

  let add_i_list l (s : sequent) =
    let s, ids = List.fold_left (fun (s, ids) (npat,f) ->
        let id, s = add_i npat f s in
        s, id :: ids
      ) (s,[]) l in
    List.rev ids, s

  let add_list l s = snd (add_i_list l s)
  
  let remove id s = S.update ~hyps:(H.remove id s.hyps) s

  let fold func s init = H.fold func s.hyps init

  let map f s  = S.update ~hyps:(H.map f s.hyps)  s
  let mapi f s = S.update ~hyps:(H.mapi f s.hyps) s

  (*------------------------------------------------------------------*)
  (* We add back manually all formulas, to ensure that definitions are 
     unrolled. *)
  (* FIXME: this seems very ineficient *)
  let reload s =
    H.fold
      (fun id f s ->
        let s = remove id s in
        match f with
          | `Reach f ->
              snd (add_formula ~force:true id f s)
          | _ ->
              let _,hyps = H.add ~force:true id f s.hyps in
              S.update ~hyps s)
      s.hyps s

  (*------------------------------------------------------------------*)
  let clear_triv s =
    let s = reload s in
    let not_triv _ = function
      | `Reach f -> not (Term.f_triv f)
      | _ -> true
    in
    S.update ~hyps:(H.filter not_triv s.hyps) s

  let pp fmt s = H.pps fmt s.hyps
  let pp_dbg fmt s = H.pps ~dbg:true fmt s.hyps
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

let set_system system s = 
  let env = Env.update ~system s.env in
  S.update ~env s

let set_ty_vars ty_vars s = 
  let env = Env.update ~ty_vars s.env in
  S.update ~env s

(*------------------------------------------------------------------*)
let filter_map_hyps func hyps =
  H.map (fun f -> func f) hyps
    
(*------------------------------------------------------------------*)
(** [pi proj s] returns the projection of [s] along [proj].
  * Global hypotheses can only be kept in the projection if we are
  * projecting from pair(s,s) to single(s), if we adopt the convention
  * that global formula hypotheses are for pair(s,s) when the system
  * is single(s). We'll do better when global formulas have system
  * annotations. *)
let pi projection s =
  let pi = function
    | `Reach t -> `Reach (Term.pi_term ~projection t)
    | h -> h
  in
  let hyps = filter_map_hyps pi s.hyps in
  let system = system s in
  let env = Env.update ~system:(SystemExpr.project projection system) s.env in
  let s =
  S.update
    ~env
    ~conclusion:(Term.pi_term ~projection s.conclusion)
    ~hyps:H.empty
    s 
  in
  let keep_global =
    SystemExpr.project Term.PLeft  system =
    SystemExpr.project Term.PRight system
  in
  (* We add back manually all formulas, to ensure that definitions are
     unrolled. *)
  H.fold
    (fun id f s ->
       match f with
         | `Reach f -> snd (Hyps.add_formula id f s)
         | _ ->
             if not keep_global then s else
             let _,hyps = H.add ~force:true id f s.hyps in
               S.update ~hyps s)
    hyps s

let set_goal a s =
  let s = S.update ~conclusion:a s in
    match Term.form_to_xatom a with
      | Some at 
        when Term.ty_xatom at = Type.Message && 
             Config.auto_intro () -> 
        Hyps.add_macro_defs s a
      | _ -> s

let init ~env ~hint_db conclusion =
  init_sequent ~env ~hint_db ~conclusion

let goal s = s.conclusion

(*------------------------------------------------------------------*)
let subst subst s =
  if subst = [] then s else
    let hyps = filter_map_hyps (Equiv.Any.subst subst) s.hyps in
    let s =
      S.update
        ~hyps:hyps
        ~conclusion:(Term.subst subst s.conclusion)
        s in

    Hyps.reload s

(*------------------------------------------------------------------*)
(** TRS *)

let get_eqs_neqs s =
  List.fold_left (fun (eqs, neqs) (atom : Term.xatom) -> match atom with
      | `Comp (`Eq,  a, b) -> Term.ESubst (a,b) :: eqs, neqs
      | `Comp (`Neq, a, b) -> eqs, Term.ESubst (a,b) :: neqs
      | _ -> assert false
    ) ([],[]) (get_eq_atoms s)

let get_trs_t s : Completion.state Utils.timeout_r =
  let eqs,_ = get_eqs_neqs s in
  Completion.complete s.env.table eqs 

let get_trs s = Tactics.timeout_get (get_trs_t s)

let eq_atoms_valid s =
  let trs = get_trs s in
  let () = dbg "trs: %a" Completion.pp_state trs in

  let _, neqs = get_eqs_neqs s in
  List.exists (fun (Term.ESubst (a, b)) ->
      if Completion.check_equalities trs [Term.ESubst (a, b)] then
        let () = dbg "dis-equality %a ≠ %a violated" Term.pp a Term.pp b in
        true
      else
        let () = dbg "dis-equality %a ≠ %a: no violation"
            Term.pp a Term.pp b in
        false)
    neqs

let literals_unsat_smt ?(slow=false) s =
  Term.pp Format.std_formatter s.conclusion; Format.printf "\n";
  Smt.literals_unsat ~slow
    s.env.table
    s.env.system
    (Vars.to_list s.env.vars)
    (get_message_atoms s)
    (get_trace_literals s)
    (* TODO: now that we can pass more general formulas than lists of atoms,
     * we don't actually need to decompose message atoms / trace literals *)
    (* since we didn't move the conclusion into the premises,
     * handle it here *)
    (Term.mk_not s.conclusion :: Hint.get_smt_db s.hint_db)


(*------------------------------------------------------------------*)
let mk_trace_cntxt s = 
  Constr.{
    table  = table s;
    system = system s;
    models = Some (get_models s);
  }

let get_hint_db s = s.hint_db

(*------------------------------------------------------------------*)
let mem_felem _ _ = false
let change_felem ?loc _ _ _ = assert false
let get_felem ?loc _ _ = assert false

(*------------------------------------------------------------------*)
let map f s : sequent =
  let f' x = f.Equiv.Babel.call Equiv.Any_t x in
  set_goal (f.Equiv.Babel.call Equiv.Local_t (goal s)) (Hyps.map f' s)

(*------------------------------------------------------------------*)
let fv s : Vars.Sv.t = 
  let h_vars = 
    Hyps.fold (fun _ f vars -> 
        Vars.Sv.union (Equiv.Any.fv f) vars
      ) s Vars.Sv.empty
  in
  Vars.Sv.union h_vars (Term.fv (goal s))

(*------------------------------------------------------------------*)
module MatchF = Match.T

(*------------------------------------------------------------------*)
module Conc  = Term.Smart
module Hyp   = Equiv.Any.Smart

(*------------------------------------------------------------------*)
type trace_sequent = t

module LocalHyps = struct
  type hyp = Equiv.local_form
  type ldecl = Ident.t * hyp
  type sequent = trace_sequent

  let (!!) = function
    | `Reach h -> h
    | `Equiv _ -> assert false

  let add p h s = Hyps.add p (`Reach h) s

  let add_i p h s = Hyps.add_i p (`Reach h) s

  let add_i_list l s =
    let l = List.map (fun (p,h) -> p,`Reach h) l in
    Hyps.add_i_list l s

  let add_list l s = snd (add_i_list l s)

  let pp_hyp = Term.pp

  let pp_ldecl ?dbg fmt (id,h) = Hyps.pp_ldecl ?dbg fmt (id,`Reach h)

  let fresh_id = Hyps.fresh_id
  let fresh_ids = Hyps.fresh_ids

  let is_hyp h s = Hyps.is_hyp (`Reach h) s

  let by_id id s = !!(Hyps.by_id id s)

  let by_name name s =
    let l,h = Hyps.by_name name s in
    l,!!h

  let mem_id = Hyps.mem_id

  let mem_name = Hyps.mem_name
  let to_list s =
    List.filter_map
      (function
         | l, `Reach h -> Some (l,h)
         | l, `Equiv _ -> None)
      (Hyps.to_list s)

  let find_opt f s =
    let f id = function
      | `Reach h -> f id h
      | `Equiv _ -> false
    in
    match Hyps.find_opt f s with
      | None -> None
      | Some (id,`Reach h) -> Some (id,h)
      | _ -> assert false

  let find_map f s =
    let f id = function
      | `Reach h -> f id h
      | `Equiv _ -> None
    in
    Hyps.find_map f s

  let exists f s =
    let f id = function
      | `Reach h -> f id h
      | `Equiv _ -> false
    in
    Hyps.exists f s

  let map f s =
    let f = function `Equiv h -> `Equiv h | `Reach h -> `Reach (f h) in
    Hyps.map f s

  let mapi f s =
    let f i = function `Equiv h -> `Equiv h | `Reach h -> `Reach (f i h) in
    Hyps.mapi f s

  let remove = Hyps.remove

  let fold f s =
    let f id h acc = match h with
      | `Equiv _ -> acc
      | `Reach h -> f id h acc
    in
    Hyps.fold f s

  let clear_triv = Hyps.clear_triv

  let pp = Hyps.pp
  let pp_dbg = Hyps.pp_dbg
end
