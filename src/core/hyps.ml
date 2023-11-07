open Utils

(*------------------------------------------------------------------*)  
module L = Location
module T = Tactics

module SE = SystemExpr
module Args = TacticsArgs
  
(*------------------------------------------------------------------*)  
type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)  
let hyp_error ~loc e = raise (T.Tactic_soft_failure (loc,e))

(*------------------------------------------------------------------*) 
module type Hyp = sig 
  type t 

  val pp_hyp     : Format.formatter -> t -> unit
  val pp_hyp_dbg : Format.formatter -> t -> unit
  val _pp_hyp    : dbg:bool -> ?context:SE.context -> Format.formatter -> t -> unit

  (** Chooses a name for a formula, depending on the formula shape. *)
  val choose_name : t -> string
    
  val htrue : t
end

(*------------------------------------------------------------------*) 
(** The system expression plays two role, giving:
    - the multi-term arity of the definition 
    - the systems used to interpret the macros in the term *)
type def = SE.t * Term.term

(** Local declaration kind -- general constructor.
    Type argument ['hyp] will be instanciated by the type of hypotheses *)
type ('hyp,_) gkind =
  | Hyp : ('hyp, 'hyp) gkind
  | Def : ('hyp,  def) gkind
      
(** Local declaration content -- general constructor. *)
type 'a gldecl_cnt = 
  | LHyp of 'a     (** hypothesis, with its name *)                  
  | LDef of def    (** a defined variable (e.g. from a let binding *)

(*------------------------------------------------------------------*) 
module type S1 = sig
  (** Hypothesis *)
  type hyp 

  (** Local declaration kind *)
  type 'a kind = (hyp,'a) gkind

  (** Local declaration content *)
  type ldecl_cnt = hyp gldecl_cnt

  (** Local declaration content *)
  type ldecl = Ident.t * ldecl_cnt

  type hyps

  (*------------------------------------------------------------------*) 
  (** [by_id id s] returns the local declaration named [id] in [s]. *)
  val by_id   : Ident.t ->            hyps -> ldecl_cnt
  val by_id_k : Ident.t -> 'a kind -> hyps -> 'a

  (** Same as [by_id], but does a look-up by name and returns the full local 
      declaration. *)
  val by_name   : Theory.lsymb ->            hyps -> Ident.t * ldecl_cnt
  val by_name_k : Theory.lsymb -> 'a kind -> hyps -> Ident.t * 'a

  (*------------------------------------------------------------------*) 
  val fresh_id  : ?approx:bool -> string      -> hyps -> Ident.t
  val fresh_ids : ?approx:bool -> string list -> hyps -> Ident.t list

  (*------------------------------------------------------------------*) 
  val _add : force:bool -> Ident.t -> ldecl_cnt -> hyps -> Ident.t * hyps

  (** Adds a local declaration, and name it according to a naming pattern. *)
  val add : Args.naming_pat -> ldecl_cnt -> hyps -> hyps
  
  (** Same as [add], but also returns the ident of the new local declaration. *)
  val add_i : Args.naming_pat -> ldecl_cnt -> hyps -> Ident.t * hyps
  
  val add_i_list :
    (Args.naming_pat * ldecl_cnt) list -> hyps -> Ident.t list * hyps
  
  val add_list : (Args.naming_pat * ldecl_cnt) list -> hyps -> hyps

  (*------------------------------------------------------------------*)
  (** Find the first local declaration satisfying a predicate. *)
  val find_opt : (ldecl -> bool) -> hyps -> ldecl option
  val find_all : (ldecl -> bool) -> hyps -> ldecl list

  (** Exceptionless. *)
  val find_map : (ldecl -> 'a option) -> hyps -> 'a option

  (** Find if there exists a local declaration satisfying a predicate. *)
  val exists : (ldecl -> bool) -> hyps -> bool

  (** Removes a formula. *)
  val remove : Ident.t -> hyps -> hyps

  val filter : (ldecl -> bool) -> hyps -> hyps

  val to_list : hyps -> ldecl list

  (*------------------------------------------------------------------*)
  (** [mem_id id s] returns true if there is a local declaration with id [id] 
      in [s]. *)
  val mem_id : Ident.t -> hyps -> bool

  (** Same as [mem_id], but does a look-up by name. *)  
  val mem_name : string  -> hyps -> bool
    
  (*------------------------------------------------------------------*)  
  (** [is_hyp f s] returns true if the formula appears inside the hypotesis
      of the sequent [s].  *)
  val is_hyp : hyp -> hyps -> bool

  (*------------------------------------------------------------------*)
  val map : ?hyp:(hyp -> hyp) -> ?def:(def -> def) -> hyps -> hyps

  val mapi :
    ?hyp:(Ident.t -> hyp -> hyp) ->
    ?def:(Ident.t -> def -> def) ->
    hyps -> hyps

  (*------------------------------------------------------------------*)
  val filter_map :
    ?hyp:(Ident.t -> hyp -> hyp option) -> 
    ?def:(Ident.t -> def -> def option) -> 
    hyps -> hyps

  (*------------------------------------------------------------------*)
  val fold      : (Ident.t -> ldecl_cnt -> 'a -> 'a) -> hyps -> 'a -> 'a
  val fold_hyps : (Ident.t -> hyp       -> 'a -> 'a) -> hyps -> 'a -> 'a

  (*------------------------------------------------------------------*)
  (** Clear trivial hypotheses *)
  val clear_triv : hyps -> hyps

  (*------------------------------------------------------------------*)
  val pp_ldecl : ?dbg:bool -> ?context:SE.context -> Format.formatter -> ldecl -> unit

  val pp_hyp : Format.formatter -> hyp  -> unit

  val pp     : Format.formatter -> hyps -> unit
  val pp_dbg : Format.formatter -> hyps -> unit
  val _pp    : dbg:bool -> Format.formatter -> hyps -> unit
end

(*------------------------------------------------------------------*)
(** [S1] with [empty] *)
module type S = sig
  include S1
  val empty : hyps
  val _pp    : dbg:bool -> ?context:SE.context -> Format.formatter -> hyps -> unit
end

(*------------------------------------------------------------------*)
module Mk (H : Hyp) : S with type hyp = H.t = struct 
  module Mid = Ident.Mid

  type hyp = H.t

  (** Local declaration kind *)
  type 'a kind = (hyp,'a) gkind

  (** Local declaration content *)
  type ldecl_cnt = hyp gldecl_cnt

  (** Local declaration content *)
  type ldecl = Ident.t * ldecl_cnt
               
  type hyps = ldecl_cnt Mid.t
    (* We are using maps from idents to hypothesis, though we do not exploit
       much that map structure. *)

  (*------------------------------------------------------------------*)
  let empty = Mid.empty
                
  (*------------------------------------------------------------------*)
  let pp_hyp = H.pp_hyp

  let pp_kind (type a) fmt (k : a kind) =
    match k with
    | Hyp -> Fmt.pf fmt "hypothesis"
    | Def -> Fmt.pf fmt "definition"

  (** only print the ldecl *kind* *)
  let pp_ldecl_cnt_kind fmt (ldc : ldecl_cnt) =
    match ldc with
    | LHyp _ -> Fmt.pf fmt "hypothesis"
    | LDef _ -> Fmt.pf fmt "definition"

  let _pp_ldecl_cnt ~dbg ?context fmt = function
    | LHyp h     -> H._pp_hyp ?context ~dbg fmt h
    | LDef (se,t) -> 
      if context <> None && SE.equal0 (oget context).set se then
        Term._pp ~dbg fmt t
      else
        Fmt.pf fmt "[%a] : %a"
          SE.pp se
          (Term._pp ~dbg) t
                 
  let pp_ldecl ?(dbg=false) ?context ppf (id,hyp) =
    let pp_id ppf = (if dbg then Ident.pp_full else Ident.pp) ppf id in
    match hyp with
    | LHyp h     ->
      Fmt.pf ppf "%t: %a@;"
        pp_id (H._pp_hyp ?context ~dbg) h
    | LDef (se,t) ->
      if context <> None && SE.equal0 (oget context).set se then
        Fmt.pf ppf "%t := %a@;" pp_id (Term._pp ~dbg) t
      else
        Fmt.pf ppf "@[<hv 2>@[<hv 2>%t :=@ [%a]@]@ : %a@]@;"
          pp_id SE.pp se 
          (Term._pp ~dbg) t

  let _pp ~dbg ?context ppf hyps =
    let pp_sep ppf () = Fmt.pf ppf "" in
    Fmt.pf ppf "@[<v 0>%a@]"
      (Fmt.list ~sep:pp_sep (pp_ldecl ~dbg ?context)) (Mid.bindings hyps)

  let pp     = _pp ~dbg:false ?context:None
  let pp_dbg = _pp ~dbg:true  ?context:None

  (*------------------------------------------------------------------*)
  let find_opt (func : ldecl -> bool) hyps =
    let exception Found of ldecl in
    try
      Mid.iter (fun id ldc ->
          if func (id,ldc) then raise (Found (id,ldc));
        ) hyps;
      None
    with Found ld -> Some ld

  let find_map (func : ldecl -> 'a option) hyps : 'a option = 
    let exception Found in
    let found = ref None in
    try
      Mid.iter (fun id ldc ->
          match func (id,ldc) with
          | None -> ()
          | Some _ as res -> found := res; raise Found
        ) hyps;
      None
    with Found -> !found

  (*------------------------------------------------------------------*)
  let ld_open (type a) ?loc ((id,ldc) : ldecl) (k : a kind) : Ident.t * a =
    match ldc, k with
    | LHyp h, Hyp -> id, h
    | LDef d, Def -> id, d
    | _ ->
      hyp_error ~loc
        (Failure
           (Fmt.str "%a is a %a and not a %a"
              Ident.pp id pp_ldecl_cnt_kind ldc pp_kind k))

  (*------------------------------------------------------------------*)
  let by_id id hyps : ldecl_cnt = Mid.find id hyps 

  let by_id_k (type a) id (k : a kind) hyps : a =
    let ldc = Mid.find id hyps in
    snd (ld_open (id,ldc) k)

  (*------------------------------------------------------------------*)
  let by_name (name : lsymb) hyps : ldecl =
    match find_opt (fun (id,_) -> Ident.name id = L.unloc name) hyps with
    | Some ld -> ld
    | None -> hyp_error ~loc:(Some (L.loc name)) (T.HypUnknown (L.unloc name))

  let by_name_k (type a) (name : lsymb) (k : a kind) hyps : Ident.t * a =
    match find_opt (fun (id,_) -> Ident.name id = L.unloc name) hyps with
    | Some ld -> ld_open ~loc:(L.loc name) ld k
    | None -> hyp_error ~loc:(Some (L.loc name)) (T.HypUnknown (L.unloc name))

  (*------------------------------------------------------------------*)
  let filter (f : ldecl -> bool) hyps = Mid.filter (fun id a -> f (id,a)) hyps
 
  let find_all (f : ldecl -> bool) hyps = Mid.bindings (filter f hyps)

  let exists (f : ldecl -> bool) hyps = Mid.exists (fun id a -> f (id,a)) hyps

  (*------------------------------------------------------------------*)
  let is_hyp (f : hyp) hyps = 
    let h = LHyp f in
    exists (fun (_,a) -> h = a) hyps
      
  let remove id hyps = Mid.remove id hyps

  let to_list hyps = Mid.bindings hyps
    
  (* Note: "_" is always fresh, to allow several unnamed hypotheses. *)
  let is_fresh name hyps =
    name = "_" || Mid.for_all (fun id' _ -> Ident.name id' <> name) hyps

  (*------------------------------------------------------------------*)
  let _fresh_id name hyps =
    let rec aux n =
      let s = name ^ string_of_int n in
      if is_fresh s hyps
      then s
      else aux (n+1)
    in
    let name = if is_fresh name hyps then name else aux 0
    in
    Ident.create name

  let fresh_id ?(approx=false) name hyps =
    let id = _fresh_id name hyps in
    if (not approx) && Ident.name id <> name && name <> "_"
    then Tactics.soft_failure (Tactics.HypAlreadyExists name)
    else id

  (*------------------------------------------------------------------*)
  let _fresh_ids names (hyps : hyps) =
    let ids, _ = List.fold_left (fun (ids,hyps) name ->
        let id = _fresh_id name hyps in
        (* We add the id to [hyps] to reserve the name *)
        (id :: ids, Mid.add id (LHyp H.htrue) hyps)
      ) ([], hyps) names in
    List.rev ids

  let fresh_ids ?(approx=false) names hyps =
    let ids = _fresh_ids names hyps in
    
    if approx then ids else
      begin
        List.iter2 (fun id name ->
            if Ident.name id <> name && name <> "_"
            then Tactics.soft_failure (Tactics.HypAlreadyExists name)
          ) ids names;
        ids
      end

  (*------------------------------------------------------------------*)
  let _add ~force id (ldc : ldecl_cnt) hyps =
    assert (not (Mid.mem id hyps)); 

    if not (is_fresh (Ident.name id) hyps) then
      hyp_error ~loc:None (T.HypAlreadyExists (Ident.name id));

    let is_hyp = match ldc with LHyp _ -> true | LDef _ -> false in
    
    (* FIXME: remove legacy behavior (which do not add a value when already present) *)
    match find_opt (fun (_,ldc') -> ldc = ldc') hyps with
    | Some (id',_) when is_hyp && not force -> id', hyps  
    | _ -> id, Mid.add id ldc hyps

  let add_formula ~force id (ldc : ldecl_cnt) (hyps : hyps) =
    let id, hyps = _add ~force id ldc hyps in
    id, hyps

  let choose_name (ldc : ldecl_cnt) : string =
    match ldc with
    | LHyp f -> H.choose_name f
    | LDef (_,t) -> 
      let ty = Term.ty t in
      if Type.equal ty Type.ttimestamp then "t" else
      if Type.equal ty Type.tindex     then "i" else
      if Type.equal ty Type.tboolean   then "b" else
      if Type.equal ty Type.tmessage   then "m" else
      (*                                 *) "x"

  let add_i npat (ldc : ldecl_cnt) hyps =
    let force, approx, name = 
      match npat with
      | Args.Unnamed  -> true , true , "_"
      | Args.AnyName  -> false, true , choose_name ldc
      | Args.Named s  -> true , false, s
      | Args.Approx s -> true , true , s
    in
    let id = fresh_id ~approx name hyps in

    add_formula ~force id ldc hyps

  let add npat (ldc : ldecl_cnt) hyps : hyps = snd (add_i npat ldc hyps)

  let add_i_list l (hyps : hyps) =
    let hyps, ids = List.fold_left (fun (hyps, ids) (npat,f) ->
        let id, hyps = add_i npat f hyps in
        hyps, id :: ids
      ) (hyps,[]) l in
    List.rev ids, hyps

  let add_list l s = snd (add_i_list l s)

  (*------------------------------------------------------------------*)
  let mem_id id hyps = Mid.mem id hyps
  let mem_name name hyps =
    Mid.exists (fun id' _ -> Ident.name id' = name) hyps

  (*------------------------------------------------------------------*)  
  let map  ?(hyp = fun x -> x) ?(def = fun x -> x) hyps = 
    Mid.map (function LHyp f -> LHyp (hyp f) | LDef t -> LDef (def t)) hyps

  let mapi ?(hyp = fun _ x -> x) ?(def = fun _ x -> x) hyps = 
    Mid.mapi (fun i -> function
        | LHyp f -> LHyp (hyp i f)
        | LDef t -> LDef (def i t)
      ) hyps
      
  (*------------------------------------------------------------------*)
  let filter_map ?(hyp = fun _ x -> Some x) ?(def = fun _ x -> Some x) hyps = 
    Mid.filter_map (fun i -> function
        | LHyp f -> omap (fun x -> LHyp x) (hyp i f)
        | LDef t -> omap (fun x -> LDef x) (def i t)
      ) hyps

  (*------------------------------------------------------------------*)
  let fold func (hyps : hyps) init = Mid.fold func hyps init

  let fold_hyps func (hyps : hyps) init = 
    Mid.fold (fun id ldc a -> 
        match ldc with
        | LHyp f -> func id f a
        | LDef _ -> a
      ) hyps init

  let clear_triv hyps = hyps
end

(*------------------------------------------------------------------*)
(** {2 Equiv Hyps} *)

module EquivHyps = Mk
    (struct
      type t = Equiv.form

      let pp_hyp     = Equiv.pp
      let _pp_hyp    = Equiv._pp
      let pp_hyp_dbg = Equiv.pp_dbg

      let choose_name _f = "H"

      let htrue = Equiv.Atom (Equiv.Equiv [])
    end)


(*------------------------------------------------------------------*)
(** {2 Trace Hyps} *)

let get_ord (at : Term.Lit.xatom ) : Term.Lit.ord =
  match at with
  | Comp (ord,_,_) -> ord
  | Happens _      -> assert false
  | Atom _ -> assert false

(*------------------------------------------------------------------*)
module TraceHyps = Mk(struct
    type t = Equiv.any_form
    let pp_hyp     = Equiv.Any.pp
    let pp_hyp_dbg = Equiv.Any.pp_dbg
    let _pp_hyp    = Equiv.Any._pp

    let htrue = Equiv.Local Term.mk_true

    let choose_name : Equiv.any_form -> string = function
      | Global _ -> "G"
      | Local f ->
        match Term.Lit.form_to_xatom f with
        | Some (Term.Lit.Comp (`Eq, _, ftrue)) when ftrue = Term.mk_true -> "H"
        | Some (Term.Lit.Atom _) | None -> "H"
        | Some (Term.Lit.Happens _) -> "Hap"
        | Some at ->
          let sort = match Term.Lit.ty_xatom at with
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
  end)


(*------------------------------------------------------------------*)
(** Collect specific local hypotheses *)
  
let get_atoms_of_hyps (hyps : TraceHyps.hyps) : Term.Lit.literals =
  TraceHyps.fold_hyps (fun _ f acc ->
      match f with
      | Local f
      | Global Equiv.(Atom (Reach f)) ->
        begin match Term.Lit.form_to_literals f with
          | `Entails lits | `Equiv lits -> lits @ acc
        end
      | Global _ -> acc
    ) hyps [] 

let get_message_atoms (hyps : TraceHyps.hyps) : Term.Lit.xatom list =
  let do1 (at : Term.Lit.literal) : Term.Lit.xatom option =
    match Term.Lit.ty at with
    | Type.Timestamp | Type.Index -> None
    | _ ->
      (* FIXME: move simplifications elsewhere *)
      match at with 
      | `Pos, (Comp _ as at)       -> Some at
      | `Neg, (Comp (`Eq, t1, t2)) -> Some (Comp (`Neq, t1, t2))
      | _ -> None
  in
  List.filter_map do1 (get_atoms_of_hyps hyps)

let get_trace_literals (hyps : TraceHyps.hyps) : Term.Lit.literals =
  let do1 (lit : Term.Lit.literal) : Term.Lit.literal option =
    match Term.Lit.ty lit with 
    | Type.Index | Type.Timestamp -> Some lit
    | _ -> None
  in
  List.filter_map do1 (get_atoms_of_hyps hyps)

let get_eq_atoms (hyps : TraceHyps.hyps) : Term.Lit.xatom list =
  let do1 (lit : Term.Lit.literal) : Term.Lit.xatom option =
    match lit with 
    | `Pos, (Comp ((`Eq | `Neq), _, _) as at) -> Some at

    | `Neg, (Comp (`Eq,  t1, t2)) -> Some (Comp (`Neq, t1, t2))
    | `Neg, (Comp (`Neq, t1, t2)) -> Some (Comp (`Eq,  t1, t2))

    | `Pos, Atom f -> Some (Comp (`Eq,  f, Term.mk_true))
    | `Neg, Atom f -> Some (Comp (`Neq, f, Term.mk_true))
                        
    | _ -> None
  in
  List.filter_map do1 (get_atoms_of_hyps hyps)

(*------------------------------------------------------------------*) 
(** {2 Changing the context of a set of hypotheses} *)

(** Internal.
    
    Common setup for to change hypotheses context.
    For each kind of hypothesis we need an update function that
    returns [None] if the hypothesis must be dropped, and [Some f]
    if it must be changed to [f].
    [setup_change_hyps_context] returns the pair of local and
    global update functions. *)
let setup_change_hyps_context 
    ~(old_context : SE.context) 
    ~(new_context : SE.context)
    ~(table : Symbols.table)
    ~(vars : Vars.env) 
  : ( Term.term ->  Term.term option) *
    (Equiv.form -> Equiv.form option)
  =
  assert (SE.compatible table new_context.SE.set old_context.SE.set);
  assert (match new_context.SE.pair with
            | Some p -> SE.compatible table new_context.SE.set p
            | None -> true);
  assert (match old_context.SE.pair with
            | Some p -> SE.compatible table old_context.SE.set p
            | None -> true);

  (* Flags indicating which parts of the context are changed. *)
  let set_unchanged = SE.equal table new_context.SE.set old_context.SE.set in
  let pair_unchanged = 
    oequal (SE.equal table) new_context.SE.pair old_context.SE.pair 
  in

  let pair_sym =
    (* DBG *)
    if new_context.SE.pair = None || old_context.SE.pair = None then false
    else
      let new_pair = oget new_context.SE.pair in
      let new_left, new_right = snd (SE.fst new_pair), snd (SE.snd new_pair) in
      let old_pair = oget old_context.SE.pair in
      let old_left, old_right = snd (SE.fst old_pair), snd (SE.snd old_pair) in
      new_left = old_right && new_right = old_left
  in
  
  (* Can we project formulas from the old to the new context? *)
  let set_projections : (Term.term -> Term.term) option =
    if SE.is_any_or_any_comp old_context.set then Some (fun f -> f) else
      if SE.subset_modulo table new_context.set old_context.set then
        match SE.(to_projs (to_fset new_context.set)) with
          | projs -> Some (fun f -> Term.project projs f)
          | exception SE.(Error (_,Expected_fset)) -> assert false
      else
        None
  in

  (* A local hypothesis can be kept with a projection from the old to
     the new system, when it exists. *)
  let update_local f =
    Utils.omap (fun project -> project f) set_projections
  in

  let rec no_diff = function
    | Term.Diff _ -> false
    | t -> Term.tforall no_diff t
  in

  (* Environment used to analyze [Reach _] atoms in hypotheses
     of the old sequent. *)
  let env =
    Env.init ~table ~vars ~system:{ old_context with pair = None; } () in
  
  (* For global hypotheses:
    - Reachability atoms are handled as local hypotheses.
    - Other global hypotheses can be kept if their meaning is unchanged
      in the new annotation. This is ensured in [can_keep_global]
      by checking the following conditions on atoms:
      + Reachability atoms are unconstrained if the set annotation
        has not changed. Otherwise they must be pure trace formulas.
      + Equivalence atoms are only allowed if the trace annotation has
        not changed. 
      + General predicates can always be kept, as their semantics 
        does not depend on the system annotation of the sequent *)
  let rec can_keep_global (env : Env.t) = function
    | Equiv.Quant (_,vars,f) ->
      let env = { env with Env.vars = Vars.add_vars vars env.vars } in
      can_keep_global env f

    | Let (v,t,f) ->
      (* [t] is taken w.r.t. [pair], hence [pair_unchanged] ensures that
         its semantics is preserved. *)
      pair_unchanged &&         
      let env =
        { env with Env.vars = Vars.add_var v (HighTerm.tag_of_term env t) env.vars }
      in
      can_keep_global env f
      
    | Impl (f,g) | Equiv.And (f,g) | Or (f,g) ->
      can_keep_global env f && can_keep_global env g

    | Atom (Equiv e) ->
      (pair_sym && List.for_all no_diff e) ||
      pair_unchanged

    | Atom (Pred _) -> true
      
    | Atom (Reach a) ->
      (HighTerm.is_constant     env a &&
       HighTerm.is_system_indep env a)
      || set_unchanged
  in
  let update_global f =
    if can_keep_global env f then Some f else
      match f with
        | Equiv.Atom (Reach f) ->
            Utils.omap (fun f -> Equiv.Atom (Reach f)) (update_local f)
        | _ -> None
  in

  update_local, update_global

(*------------------------------------------------------------------*) 
(** See `.mli` *)
let change_trace_hyps_context
    ?update_local
    ~(old_context : SE.context) 
    ~(new_context : SE.context)
    ~(table : Symbols.table)
    ~(vars : Vars.env) 
    (hyps : TraceHyps.hyps)
  : TraceHyps.hyps
  =
  let default_update_local,update_global =
    setup_change_hyps_context 
      ~old_context ~new_context ~vars ~table
  in
  let update_local = odflt default_update_local update_local in

  TraceHyps.filter_map
    ~hyp:(fun _ f ->
        match f with
        | Local  f -> omap (fun x -> Equiv.Local  x) (update_local  f)
        | Global f -> omap (fun x -> Equiv.Global x) (update_global f)
      )
    ~def:(fun _ (se,t) -> Some (se,t))
    (* changing the context does not impact definitions, as these come
       with their own context *)
    hyps

(*------------------------------------------------------------------*) 
(** See `.mli` *)
let change_equiv_hyps_context 
    ~(old_context : SE.context) 
    ~(new_context : SE.context)
    ~(table : Symbols.table)
    ~(vars : Vars.env) 
    (hyps : EquivHyps.hyps)
  : EquivHyps.hyps
  =
  let _update_local,update_global =
    setup_change_hyps_context
      ~old_context ~new_context ~vars ~table
  in
  EquivHyps.filter_map
    ~hyp:(fun _ f -> update_global f)
    ~def:(fun _ (se,t) -> Some (se,t))
    (* changing the context does not impact definitions, as these come
       with their own context *)
    hyps 

