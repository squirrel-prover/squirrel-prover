open Utils
open Atom

type hyp_error =
  | HypAlreadyExists of string
  | HypUnknown of string
      
exception Hyp_error of hyp_error
                     
let hyp_error e = raise (Hyp_error e)

let pp_hyp_error fmt = function
  | HypAlreadyExists s ->
    Fmt.pf fmt "an hypothesis named %s already exists" s     
  | HypUnknown s ->
    Fmt.pf fmt "unknown hypothesis %s" s     

(*------------------------------------------------------------------*)  
type hyp = Term.formula
                
let pp_hyp fmt f = Term.pp fmt f
                         
type ldecl = Ident.t * hyp

let pp_ldecl ?(dbg=false) ppf (id,hyp) =
  Fmt.pf ppf "%a: %a@;"
    (if dbg then Ident.pp_full else Ident.pp) id
    pp_hyp hyp
    
module H : sig
  type hyps

  val empty : hyps

  val is_hyp : Term.formula -> hyps -> bool
    
  val by_id   : Ident.t -> hyps -> hyp
  val by_name : string  -> hyps -> ldecl

  val hyp_by_name : string  -> hyps -> hyp
  val id_by_name  : string  -> hyps -> Ident.t

  val fresh_id : string -> hyps -> Ident.t
  val fresh_ids : string list -> hyps -> Ident.t list
  
  val add : force:bool -> Ident.t -> hyp -> hyps -> hyps

  val find_opt : (Ident.t -> hyp -> bool) -> hyps -> ldecl option
  val find_all : (Ident.t -> hyp -> bool) -> hyps -> ldecl list

  val find_map : (Ident.t -> hyp -> 'a option) -> hyps -> 'a option
    
  val exists : (Ident.t -> hyp -> bool) -> hyps -> bool
    
  val remove : Ident.t -> hyps -> hyps

  val filter : (Ident.t -> hyp -> bool) -> hyps -> hyps

  val to_list : hyps -> ldecl list

  val mem_id   : Ident.t -> hyps -> bool
  val mem_name : string  -> hyps -> bool

  val map :  (hyp ->  hyp) -> hyps -> hyps

  val fold : (Ident.t -> Term.formula -> 'a -> 'a) -> hyps -> 'a -> 'a
    
  val pps : ?dbg:bool -> Format.formatter -> hyps -> unit

end = struct 
  module Mid = Ident.Mid

  (* We are using maps from idents to hypothesis, though we do not exploit
     much that map structure. *)
  type hyps = hyp Mid.t
  
  let empty =  Mid.empty

  let pps ?(dbg=false) ppf hyps =
    let pp_sep fmt () = Fmt.pf ppf "" in
    Fmt.pf ppf "@[<v 0>%a@]"
      (Fmt.list ~sep:pp_sep (pp_ldecl ~dbg)) (Mid.bindings hyps)
      
  let find_opt func hyps =
    let exception Found of Ident.t * hyp in
    try
      Mid.iter (fun id a ->
          if func id a then raise (Found (id,a)) else ()
        ) hyps ;
      None
    with Found (id,a) -> Some (id,a)

  let find_map (func : Ident.t -> Term.formula -> 'a option) hyps = 
    let exception Found in
    let found = ref None in
    try
      Mid.iter (fun id a -> match func id a with
          | None -> ()
          | Some _ as res -> found := res; raise Found
        ) hyps ;
      None
    with Found -> !found

  let by_id id hyps =
    try Mid.find id hyps
    with Not_found -> hyp_error (HypUnknown (Ident.to_string id))
  (* the latter case should not happen *)

  let by_name name hyps =
    match find_opt (fun id _ -> Ident.name id = name) hyps with
    | Some (id,f) -> id, f
    | None -> hyp_error (HypUnknown name)

  let hyp_by_name name hyps = snd (by_name name hyps)
  let id_by_name name hyps  = fst (by_name name hyps)

  let filter f hyps = Mid.filter (fun id a -> f id a) hyps
 
  let find_all f hyps = Mid.bindings (filter f hyps)

  let exists f hyps = Mid.exists f hyps

  let is_hyp f hyps = exists (fun _ f' -> f = f') hyps
      
  let remove id hyps = Mid.remove id hyps

  let to_list hyps = Mid.bindings hyps
    
  (* Note: "_" is always fresh, to allow several unnamed hypotheses. *)
  let is_fresh name hyps =
    name = "_" || Mid.for_all (fun id' _ -> Ident.name id' <> name) hyps
      
  let fresh_id name hyps =
    let rec aux n =
      let s = name ^ string_of_int n in
      if is_fresh s hyps
      then s
      else aux (n+1)
    in
    let name = if is_fresh name hyps then name else aux 0
    in
    Ident.create name

  let fresh_ids names hyps =
    let ids, _ = List.fold_left (fun (ids,hyps) name ->
        let id = fresh_id name hyps in
        (* We add the id to [hyps] to reserve the name *)
        (id :: ids, Mid.add id Term.True hyps)
      ) ([], hyps) names in
    List.rev ids
    
  let add ~force id hyp hyps =
    assert (not (Mid.mem id hyps)); 
    if not (is_fresh (Ident.name id) hyps)
    then hyp_error (HypAlreadyExists (Ident.name id))
    (* do we really want to not add twice an hypothesis ? *)
    else if is_hyp hyp hyps && not force then hyps else Mid.add id hyp hyps
  
  let mem_id id hyps = Mid.mem id hyps
  let mem_name name hyps =
    Mid.exists (fun id' _ -> Ident.name id' = name) hyps
  
  let map f hyps = Mid.map (fun h -> f h) hyps

  let fold func hyps init = Mid.fold func hyps init 
end

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
      trs = trs ;
      models = models ; }
  
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
module Hyps = struct
  let fresh_id ?(approx=false) name s =
    let id = H.fresh_id name s.hyps in
    if (not approx) && Ident.name id <> name && name <> "_"
    then hyp_error (HypAlreadyExists name) 
    else id

  let fresh_ids ?(approx=false) names s =
    let ids = H.fresh_ids names s.hyps in
    
    if approx then ids else
      begin
        List.iter2 (fun id name ->
            if Ident.name id <> name && name <> "_"
            then hyp_error (HypAlreadyExists name)
          ) ids names;
        ids
      end

  let is_hyp f s = H.is_hyp f s.hyps

  let by_id   id s = H.by_id   id s.hyps
  let by_name id s = H.by_name id s.hyps

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
          f t def ;
          self#visit_message def
      | t -> super#visit_message t
    method visit_formula f =
      (* Do not visit macros. When a macro formula is defined we could add
       * an hyp stating the equivalence between the macro and its
       * expansion. But we'll probably take care of that later as part of a
       * larger redesign of the macro expansion system. *)
      match f with
      | Term.Macro ((m,sort,is),[],a) -> ()
      | t -> super#visit_formula t
  end

  (** Add to [s] equalities corresponding to the expansions of all macros
    * occurring in [at]. *)
  let rec add_macro_defs s at =
    let macro_eqs : message_atom list ref = ref [] in
    let iter =
      new iter_macros
        ~system:s.system
        s.table
        (fun t t' -> macro_eqs := `Message (`Eq,t,t') :: !macro_eqs) in
    
    iter#visit_formula (Term.Atom at) ;
    
    List.fold_left (add_message_atom None) s !macro_eqs

  and add_message_atom ?(force=false) (id : Ident.t option) s at =
    let f = Term.Atom (at :> generic_atom) in
    let recurse = not (H.is_hyp f s.hyps) in
    
    (* TODO: remove auto naming ? *)
    let id = match id with       
      | None -> H.fresh_id "D" s.hyps
      | Some id -> id in
    let hyps = H.add ~force id f s.hyps in
    let s =
      S.update ~keep_trs:false ~keep_models:true
        ~hyps s in

    (* [recurse] boolean to avoid looping *)
    if recurse then add_macro_defs s (at :> generic_atom) else s

  let rec add_happens ?(force=false) id s ts =
    let f = Term.Atom (`Happens ts :> generic_atom) in
    let hyps = H.add ~force id f s.hyps in
    let s =
      S.update ~keep_trs:true ~keep_models:false
        ~hyps s in
    
    match ts with
    | Term.Action (symb,indices) ->
      let a = Action.of_term symb indices s.table in
      let system = s.system in
      let table  = s.table in
      
      (* TODO: remove auto naming ? *)
      add_formula (H.fresh_id "C" s.hyps)
        (snd (SystemExpr.descr_of_action table system a).Action.condition)
        s
    | _ -> s

  (** if [force], we add the formula to [Hyps] even if it already exists. *)
  and add_formula ?(force=false) id f s =
    match f with
    | Term.Atom (#Atom.message_atom as at) -> add_message_atom ~force (Some id) s at
    | Term.Atom (`Happens ts)              -> add_happens ~force id s ts
    | _ ->
      let hyps = H.add ~force id f s.hyps in
      (* TODO: performances, less updates ? *)
      S.update ~hyps:hyps s

  let add_formula id f s = add_formula ~force:true id f s
  
  let remove id s = S.update ~hyps:(H.remove id s.hyps) s

  let fold func s init = H.fold func s.hyps init

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
let atom_triv = function
  | `Message   (`Eq,t1,t2) when t1=t2 -> true
  | `Timestamp (`Eq,t1,t2) when t1=t2 -> true
  | `Index     (`Eq,i1,i2) when i1=i2 -> true
  | _ -> false 

let f_triv = function
  | Term.True -> true
  | Term.Atom atom -> atom_triv atom
  | _ -> false 

let filter_map_hyps func hyps =
  H.map (fun f -> func f) hyps
  |> H.filter (fun _ f -> not (f_triv f))
    
(*------------------------------------------------------------------*)
let pi projection s =
  let pi_term t = Term.pi_term ~projection t in
  S.update
    ~conclusion:(pi_term s.conclusion)
    ~hyps:(filter_map_hyps pi_term s.hyps)
    ~keep_trs:false
    ~keep_models:false
    s

let set_conclusion a s =
  let s = S.update ~conclusion:a s in
    match a with
      | Term.Atom (#message_atom as at) -> Hyps.add_macro_defs s at
      | _ -> s

let init ~system table (goal : Term.formula) =
  set_conclusion goal (init_sequent system table)

let conclusion s = s.conclusion

(*------------------------------------------------------------------*)
let subst subst s =
  if subst = [] then s else
    S.update
      ~hyps:(filter_map_hyps (Term.subst subst) s.hyps)
      ~conclusion:(Term.subst subst s.conclusion)
      s

(*------------------------------------------------------------------*)
let get_message_atoms s =
  List.fold_left (fun atoms (_,hyp) -> match hyp with
      | Term.Atom (`Message atom) -> atom :: atoms
      | _ -> atoms
    ) [] (H.to_list s.hyps)

let get_trace_atoms s =
  List.fold_left (fun atoms (id,hyp) -> match hyp with
      | Term.Atom (`Timestamp a as atom) -> atom :: atoms
      | Term.Atom (`Index a     as atom) -> atom :: atoms
      | _ -> atoms
    ) [] (H.to_list s.hyps)

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
    let _, neqs = get_eqs_neqs s in
    Result (
      List.exists (fun eq ->
          Completion.check_equalities trs [eq])
        neqs)

(*------------------------------------------------------------------*)
(** Constraints *)

let get_models s : Constr.models timeout_r =
  match !(s.models) with
  | Some models -> Result models
  | None ->
    let trace_atoms = get_trace_atoms s in
    match Constr.models_conjunct trace_atoms with
    | Timeout -> Timeout
    | Result models ->
      let () = S.set_models s models in
      Result models

let maximal_elems s tss =
  match get_models s with
  | Result models -> Result (Constr.maximal_elems models tss)
  | Timeout -> Timeout

let get_ts_equalities s =
  match get_models s with
  | Result models ->
    let ts = trace_atoms_ts (get_trace_atoms s) in
    Result (Constr.get_ts_equalities models ts)
  | Timeout -> Timeout

let get_ind_equalities s =
  match get_models s with
  | Result models ->
    let inds = trace_atoms_ind (get_trace_atoms s) in
    Result (Constr.get_ind_equalities models inds)
  | Timeout -> Timeout    

let constraints_valid s =
  match get_models s with
  | Result models -> Result (not (Constr.m_is_sat models))
  | Timeout -> Timeout

(*------------------------------------------------------------------*)
let get_all_terms s =
  let atoms = get_message_atoms s in
  let atoms =
    match s.conclusion with
      | Term.Atom (`Message atom) -> atom::atoms
      | _ -> atoms
  in
  List.fold_left (fun acc (_,a,b) -> a :: b :: acc) [] atoms
