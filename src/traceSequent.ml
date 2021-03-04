open Utils

module Args = TacticsArgs

module L = Location

(*------------------------------------------------------------------*)
(* For debugging *)
let dbg s = Printer.prt `Ignore s
(* let dbg s = Printer.prt `Dbg s *)

(*------------------------------------------------------------------*)
let get_ord (at : Term.generic_atom ) : Term.ord option = match at with
  | `Timestamp (ord,_,_) -> Some ord
  | `Message   (ord,_,_) -> Some (ord :> Term.ord)
  | `Index     (ord,_,_) -> Some (ord :> Term.ord)
  | `Happens _           -> None

let prefix_count_regexp = Pcre.regexp "([^0-9]*)([0-9]*)"

(** Chooses a name for a formula, depending on an old name (if any), and the
    formula shape. *)
let choose_name f = match f with
  | Term.Atom at ->
    let sort = match at with
      | `Timestamp _ -> "C"
      | `Message _ -> "M"
      | `Index _ -> "I"
      | `Happens _ -> "Hap" in

    let ord = match get_ord at with
      | Some `Eq  -> "eq"
      | Some `Neq -> "neq"
      | Some `Leq -> "le"
      | Some `Geq -> "ge"
      | Some `Lt  -> "lt"
      | Some `Gt  -> "gt"
      | None      -> "" in

    sort ^ ord

  | _ -> "H"

(*------------------------------------------------------------------*)
let atom_triv = function
  | `Message   (`Eq,t1,t2) when t1=t2 -> true
  | `Timestamp (`Eq,t1,t2) when t1=t2 -> true
  | `Index     (`Eq,i1,i2) when i1=i2 -> true
  | _ -> false 

let f_triv = function
  | Term.True -> true
  | Term.Atom atom -> atom_triv atom
  | _ -> false 

(*------------------------------------------------------------------*)
module FHyp = struct
  type t = Term.formula
  let pp_hyp fmt f = Term.pp fmt f

  let htrue = Term.True
end

module H = Hyps.Mk(FHyp)

(*------------------------------------------------------------------*)
module S : sig
  type t = private {
    system : SystemExpr.system_expr ;
    table : Symbols.table;
    env : Vars.env;
    (** Must contain all free variables of the sequent,
      * which are logically understood as universally quantified. *)
    
    hyps : H.hyps;
    (** Hypotheses *)
    
    conclusion : Term.formula;
    (** The conclusion / right-hand side formula of the sequent. *)
    
    trs : Completion.state option ref;
    (** Either [None], or the term rewriting system
      * corresponding to the current message hyps.
      * Must be se to [None] if message hyps change. 
      * We use a reference to try to share the TRS accross 
      * multiple sequents. *)
    
    models : Constr.models option ref;
    (** Either [None], or the models corresponding to the current
      * trace hyps.
      * Must be set to [None] if trace hyps change. 
      * We use a reference to try to share the models accross 
      * multiple sequents. *)
  }

  val init_sequent : SystemExpr.system_expr -> Symbols.table -> t

  (** Updates a sequent.
      [keep_trs] must be [true] only if the udates leaves the TRS associated to
      the sequent unchanged.
      Idem for [keep_models] and the models.
      [keep_trs] and [keep_models] default to [false]. *)
  val update :
    ?system:SystemExpr.system_expr ->
    ?table:Symbols.table ->
    ?env:Vars.env ->
    ?hyps:H.hyps ->
    ?conclusion:Term.formula ->
    ?keep_trs:bool ->
    ?keep_models:bool -> 
    t -> t

  (** Set the trs of a sequent. 
      Raise [Invalid_argument ..] if already set. *)
  val set_trs : t -> Completion.state -> unit

  (** Set the models of a sequent. 
      Raise [Invalid_argument ..] if already set. *)
  val set_models : t -> Constr.models -> unit
end = struct
  type t = {
    system       : SystemExpr.system_expr ;
    table        : Symbols.table;
    env          : Vars.env;
    hyps         : H.hyps;
    conclusion   : Term.formula;
    trs          : Completion.state option ref;
    models       : Constr.models option ref;
  }

  let init_sequent system table = {
    system       = system ;
    table        = table;
    env          = Vars.empty_env;
    hyps         = H.empty;
    conclusion   = Term.True;
    trs          = ref None;
    models       = ref None;
  }

  let update ?system ?table ?env ?hyps
      ?conclusion ?(keep_trs=false) ?(keep_models=false) t =
    let trs = 
      if keep_trs || hyps = None 
      then t.trs 
      else ref None 
    and models =
      if keep_models || hyps = None 
      then t.models
      else ref None 
    in
    let system       = Utils.odflt t.system system
    and table        = Utils.odflt t.table table
    and env          = Utils.odflt t.env env
    and hyps         = Utils.odflt t.hyps hyps
    and conclusion   = Utils.odflt t.conclusion conclusion in
    { system = system ;
      table = table ;
      env = env ;
      hyps = hyps ;
      conclusion = conclusion ;
      trs = trs ;               (* FIXME: right now this is useless *)
      models = models ;         (* FIXME: right now this is useless *) }
  
  let set_trs t trs = match !(t.trs) with
    | None -> t.trs := Some trs
    | Some _ -> raise (Invalid_argument "traceSequent: trs already set")

  let set_models t models = match !(t.models) with
    | None -> t.models := Some models
    | Some _ -> raise (Invalid_argument "traceSequent: models already set")
end

include S

type sequent = S.t

let pp ppf s =
  let open Fmt in
  pf ppf "@[<v 0>" ;
  pf ppf "@[System: %a@]@;"
    SystemExpr.pp_system s.system;
  if s.env <> Vars.empty_env then
    pf ppf "@[Variables: %a@]@;" Vars.pp_env s.env ;
  (* Print hypotheses *)
  H.pps ppf s.hyps ;

  (* Print separation between hyps and conclusion *)
  styled `Bold ident ppf (String.make 40 '-') ;
  (* Print conclusion formula and close box. *)
  pf ppf "@;%a@]" Term.pp s.conclusion


(*------------------------------------------------------------------*)
let rec simpl_form acc hyp = 
  match hyp with
  | Term.And (f,g) -> simpl_form (simpl_form acc f) g

  | Exists (vs,f) ->
    let subst =
      List.map
        (fun (Vars.EVar v) ->
           Term.ESubst  (Term.Var v,
                         Term.Var (Vars.make_new_from v)))
        vs
    in
    let f = Term.subst subst f in
    simpl_form acc f

  | _ as f -> f :: acc

(*------------------------------------------------------------------*)
let get_message_atoms s =
  let hyps = H.fold (fun _ f acc -> simpl_form acc f) s.hyps [] in
  List.fold_left (fun atoms hyp -> match hyp with 
      | Term.(Atom (`Message at)) -> at :: atoms
      | Term.(Not (Atom (#message_atom as at))) ->
        let `Message neg_at = Term.not_message_atom at in
        neg_at :: atoms
      | _ -> atoms
    ) [] hyps

let get_trace_literals s =
  let hyps = H.fold (fun _ f acc -> simpl_form acc f) s.hyps [] in
  List.fold_left (fun atoms hyp -> match hyp with
      | Term.(Atom (#trace_atom as at)) ->
        (`Pos, at) :: atoms
      | Term.(Not (Atom (#trace_atom as at))) ->
        (`Neg, at) :: atoms
      | _ -> atoms
    ) [] hyps

(*------------------------------------------------------------------*)
(** Prepare constraints or TRS query *)

let get_models s : Constr.models timeout_r =
  match !(s.models) with
  | Some models -> Result models
  | None ->
    let trace_literals = get_trace_literals s in
    match Constr.models_conjunct trace_literals with
    | Timeout -> Timeout
    | Result models ->
      let () = S.set_models s models in
      Result models

let query ~precise s q =
  let models = Tactics.timeout_get (get_models s) in
  Constr.query ~precise models q

let query_happens ~precise s a = query ~precise s [`Pos, `Happens a]

let maximal_elems ~precise s tss =
  match get_models s with
  | Result models -> Result (Constr.maximal_elems ~precise models tss)
  | Timeout -> Timeout

let get_ts_equalities ~precise s =
  match get_models s with
  | Result models ->
    let ts = List.map (fun (_,x) -> x) (get_trace_literals s)
             |>  Atom.trace_atoms_ts in
    Result (Constr.get_ts_equalities ~precise models ts)
  | Timeout -> Timeout

let get_ind_equalities ~precise s =
  match get_models s with
  | Result models ->
    let inds = List.map (fun (_,x) -> x) (get_trace_literals s)
               |> Atom.trace_atoms_ind in
    Result (Constr.get_ind_equalities ~precise models inds)
  | Timeout -> Timeout    

let constraints_valid s =
  match get_models s with
  | Result models -> Result (not (Constr.m_is_sat models))
  | Timeout -> Timeout

(*------------------------------------------------------------------*)
let get_all_messages s =
  let atoms = get_message_atoms s in
  let atoms =
    match s.conclusion with
      | Term.Atom (`Message atom) -> atom :: atoms
      | _ -> atoms
  in
  List.fold_left (fun acc (_,a,b) -> a :: b :: acc) [] atoms

(* (\*------------------------------------------------------------------*\)
 * let get_all_terms s =
 *   let atoms = get_message_atoms s in
 *   let atoms =
 *     match s.conclusion with
 *       | Term.Atom (`Message atom) -> atom :: atoms
 *       | _ -> atoms
 *   in
 *   List.fold_left (fun acc (_,a,b) -> a :: b :: acc) [] atoms *)

(*------------------------------------------------------------------*)  
module Hyps 
  (* : Hyps.HypsSeq with type hyp = Term.formula and type sequent = t *)
= struct
  type sequent = t

  type hyp = Term.formula

  type ldecl = Ident.t * hyp

  let pp_hyp = Term.pp 
  let pp_ldecl = H.pp_ldecl

  let fresh_id ?(approx=false) name s =
    let id = H.fresh_id name s.hyps in
    if (not approx) && Ident.name id <> name && name <> "_"
    then Hyps.hyp_error ~loc:None (Hyps.HypAlreadyExists name) 
    else id

  let fresh_ids ?(approx=false) names s =
    let ids = H.fresh_ids names s.hyps in
    
    if approx then ids else
      begin
        List.iter2 (fun id name ->
            if Ident.name id <> name && name <> "_"
            then Hyps.hyp_error ~loc:None (Hyps.HypAlreadyExists name)
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

  class iter_macros ~system table f = object (self)
    inherit Iter.iter ~system table as super
    method visit_message t =
      match t with
      | Term.Macro ((m,sort,is),[],a) ->
        if List.for_all
            Vars.(function EVar v -> not (is_new v))
            (Term.get_vars t) &&
           Macros.is_defined m a table
        then
          let def = Macros.get_definition system table sort m is a in
          f a (`Message (t, def)) ;
          self#visit_message def
      | t -> super#visit_message t
    method visit_formula t = 
      match t with
      | Term.Macro ((m,sort,is),[],a) -> 
        if List.for_all
            Vars.(function EVar v -> not (is_new v))
            (Term.get_vars t) &&
           Macros.is_defined m a table
        then
          let def = Macros.get_definition system table sort m is a in
          f a (`Boolean (t, def)) ;
          self#visit_formula def
      | t -> super#visit_formula t
  end

  (** Add to [s] equalities corresponding to the expansions of all macros
    * occurring in [f], if [f] happened. *)
  let rec add_macro_defs (s : sequent) f =
    let macro_eqs : (Term.timestamp * Term.formula) list ref = ref [] in
    let iter =
      new iter_macros
        ~system:s.system
        s.table
        (fun a el -> match el with
           |`Message (t,t') ->
             macro_eqs := (a, Term.Atom (`Message (`Eq,t,t'))) :: !macro_eqs
           |`Boolean (f,f') -> () (* TODO: add that f <=> f' *)
        ) in
    
    iter#visit_formula f ;
    
    List.fold_left (fun s (a,f) -> 
        if query_happens ~precise:true s a 
        then snd (add_form_aux None s f)
        else s
      ) s !macro_eqs

  and add_form_aux
      ?(force=false) (id : Ident.t option) (s : sequent) (f : Term.formula) =
    let recurse = not (H.is_hyp f s.hyps) && (Config.auto_intro ()) in

    (* TODO: remove auto naming ? *)
    let id = match id with       
      | None -> H.fresh_id "D" s.hyps
      | Some id -> id in

    let id, hyps = H.add ~force id f s.hyps in
    let s =
      S.update ~keep_trs:false ~keep_models:false
        ~hyps s in
    
    (* [recurse] boolean to avoid looping *)
    let s = if recurse then add_macro_defs s f else s in

    id, s

  let add_happens ?(force=false) id (s : sequent) ts =
    let f = Term.Atom (`Happens ts :> Term.generic_atom) in
    let id, hyps = H.add ~force id f s.hyps in
    let s =
      S.update ~keep_trs:true ~keep_models:false
        ~hyps s in

    id, s

  (** if [force], we add the formula to [Hyps] even if it already exists. *)
  let add_formula ?(force=false) id f (s : sequent) =
    match f with
    | Term.Atom (#Term.message_atom) -> add_form_aux ~force (Some id) s f
    | Term.Atom (`Happens ts)        -> add_happens ~force id s ts
    | _ -> add_form_aux ~force (Some id) s f

  let add_i npat f s =
    let force, approx, name = match npat with
      | Args.Unnamed -> true, true, "_"
      | Args.AnyName -> false, true, choose_name f
      | Args.Named s -> true, false, s in

    let id = fresh_id ~approx name s in
    
    add_formula ~force id f s

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
    H.fold (fun id f s ->
        let s = remove id s in        
        snd (add_formula id f s)) s.hyps s

  (*------------------------------------------------------------------*)
  let clear_triv s = 
    let s = reload s in
    S.update ~hyps:(H.filter (fun _ f -> not (f_triv f)) s.hyps) s

  let pp fmt s = H.pps fmt s.hyps
  let pp_dbg fmt s = H.pps ~dbg:true fmt s.hyps
end

(*------------------------------------------------------------------*)
let env    s = s.env
let system s = s.system
let table  s = s.table

let set_env    a      s = S.update ~env:a         s
let set_system system s = S.update ~system:system s 
let set_table  table  s = S.update ~table:table   s 

(*------------------------------------------------------------------*)
let filter_map_hyps func hyps =
  H.map (fun f -> func f) hyps
    
(*------------------------------------------------------------------*)
let pi projection s =
  let pi_term t = Term.pi_term ~projection t in

  let hyps = filter_map_hyps pi_term s.hyps in
  let s = 
  S.update
    ~conclusion:(pi_term s.conclusion)
    ~hyps:H.empty
    ~keep_trs:false
    ~keep_models:false
    s in

  (* We add back manually all formulas, to ensure that definitions are 
     unrolled. *)
  H.fold (fun id f s -> snd (Hyps.add_formula id f s)) hyps s
  
let set_conclusion a s =
  let s = S.update ~conclusion:a s in
    match a with
      | Term.Atom Term.(#message_atom) -> Hyps.add_macro_defs s a
      | _ -> s

let init ~system table (goal : Term.formula) =
  set_conclusion goal (init_sequent system table)

let conclusion s = s.conclusion

(*------------------------------------------------------------------*)
let subst subst s =
  if subst = [] then s else
    let hyps = filter_map_hyps (Term.subst subst) s.hyps in
    let s =
      S.update
        ~hyps:hyps
        ~conclusion:(Term.subst subst s.conclusion)
        s in

    Hyps.reload s


(*------------------------------------------------------------------*)
(** TRS *)

let get_eqs_neqs s =
  List.fold_left (fun (eqs, neqs) atom -> match atom with
      | `Eq,  a, b -> (a,b) :: eqs, neqs
      | `Neq, a, b -> eqs, (a,b) :: neqs
    ) ([],[]) (get_message_atoms s)

let get_trs s : Completion.state timeout_r =
  match !(s.trs) with
  | Some trs -> Result trs
  | None ->
    let eqs,_ = get_eqs_neqs s in
    match Completion.complete s.table eqs with
    | Timeout -> Timeout
    | Result trs ->
      let () = S.set_trs s trs in
      Result trs


let message_atoms_valid s =
  match get_trs s with
  | Timeout -> Timeout
  | Result trs ->
    let () = dbg "trs: %a" Completion.pp_state trs in

    let _, neqs = get_eqs_neqs s in
    Result (
      List.exists (fun eq ->
          if Completion.check_equalities trs [eq] then
            let () = dbg "dis-equality %a ≠ %a violated" 
                Term.pp (fst eq) Term.pp (snd eq) in
            true
          else false)
        neqs)
