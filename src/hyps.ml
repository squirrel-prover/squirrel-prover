module L = Location
module T = Tactics

module Args = TacticsArgs
  
type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)  
let hyp_error ~loc e = raise (T.Tactic_soft_failure (loc,e))

(*------------------------------------------------------------------*) 
module type Hyp = sig 
  type t 

  val pp_hyp     :             Format.formatter -> t -> unit
  val _pp_hyp    : dbg:bool -> Format.formatter -> t -> unit
  val pp_hyp_dbg :             Format.formatter -> t -> unit

  (** Chooses a name for a formula, depending on the formula shape. *)
  val choose_name : t -> string
    
  val htrue : t
end

(*------------------------------------------------------------------*) 
module type S1 = sig
  (** Hypothesis *)
  type hyp 

  (** Local declaration *)
  type ldecl = Ident.t * hyp

  type hyps

  (*------------------------------------------------------------------*) 
  (** [by_id id s] returns the hypothesis with id [id] in [s]. *)
  val by_id : Ident.t -> hyps -> hyp

  (** Same as [by_id], but does a look-up by name and returns the full local 
      declaration. *)
  val by_name : lsymb   -> hyps -> ldecl

  (*------------------------------------------------------------------*) 
  val fresh_id  : ?approx:bool -> string      -> hyps -> Ident.t
  val fresh_ids : ?approx:bool -> string list -> hyps -> Ident.t list

  (*------------------------------------------------------------------*) 
  val _add : force:bool -> Ident.t -> hyp -> hyps -> Ident.t * hyps

  (** Adds a hypothesis, and name it according to a naming pattern. *)
  val add : Args.naming_pat -> hyp -> hyps -> hyps
  
  (** Same as [add], but also returns the ident of the added hypothesis. *)
  val add_i : Args.naming_pat -> hyp -> hyps -> Ident.t * hyps
  
  val add_i_list :
    (Args.naming_pat * hyp) list -> hyps -> Ident.t list * hyps
  
  val add_list   : (Args.naming_pat * hyp) list -> hyps -> hyps

  (*------------------------------------------------------------------*)
  (** Find the first local declaration satisfying a predicate. *)
  val find_opt : (Ident.t -> hyp -> bool) -> hyps -> ldecl option
  val find_all : (Ident.t -> hyp -> bool) -> hyps -> ldecl list

  (** Exceptionless. *)
  val find_map : (Ident.t -> hyp -> 'a option) -> hyps -> 'a option

  (** Find if there exists a local declaration satisfying a predicate. *)
  val exists : (Ident.t -> hyp -> bool) -> hyps -> bool

  (** Removes a formula. *)
  val remove : Ident.t -> hyps -> hyps

  val filter : (Ident.t -> hyp -> bool) -> hyps -> hyps

  val to_list : hyps -> ldecl list

  (*------------------------------------------------------------------*)
  (** [mem_id id s] returns true if there is an hypothesis with id [id] 
      in [s]. *)
  val mem_id : Ident.t -> hyps -> bool

  (** Same as [mem_id], but does a look-up by name. *)  
  val mem_name : string  -> hyps -> bool

  (*------------------------------------------------------------------*)  
  (** [is_hyp f s] returns true if the formula appears inside the hypotesis
      of the sequent [s].  *)
  val is_hyp : hyp -> hyps -> bool

  (*------------------------------------------------------------------*)
  val map  :  (hyp ->  hyp) -> hyps -> hyps
  val mapi :  (Ident.t -> hyp ->  hyp) -> hyps -> hyps

  val fold : (Ident.t -> hyp -> 'a -> 'a) -> hyps -> 'a -> 'a

  (*------------------------------------------------------------------*)
  (** Clear trivial hypotheses *)
  val clear_triv : hyps -> hyps

  (*------------------------------------------------------------------*)
  val pp_ldecl : ?dbg:bool -> Format.formatter -> ldecl -> unit

  val pp_hyp   : Format.formatter -> hyp  -> unit

  val pp       :             Format.formatter -> hyps -> unit
  val _pp      : dbg:bool -> Format.formatter -> hyps -> unit
  val pp_dbg   :             Format.formatter -> hyps -> unit
end

(*------------------------------------------------------------------*)
(** [S1] with [empty] *)
module type S = sig
  include S1
  val empty : hyps
end

(*------------------------------------------------------------------*)
module Mk (Hyp : Hyp) : S with type hyp = Hyp.t = struct 
  module Mid = Ident.Mid

  type hyp = Hyp.t
  type ldecl = Ident.t * hyp

  (* We are using maps from idents to hypothesis, though we do not exploit
     much that map structure. *)
  type hyps = hyp Mid.t

  (*------------------------------------------------------------------*)
  let empty =  Mid.empty

  let pp_hyp = Hyp.pp_hyp
                 
  let pp_ldecl ?(dbg=false) ppf (id,hyp) =
    Fmt.pf ppf "%a: %a@;"
      (if dbg then Ident.pp_full else Ident.pp) id
      (Hyp._pp_hyp ~dbg) hyp

  let _pp ~dbg ppf hyps =
    let pp_sep ppf () = Fmt.pf ppf "" in
    Fmt.pf ppf "@[<v 0>%a@]"
      (Fmt.list ~sep:pp_sep (pp_ldecl ~dbg)) (Mid.bindings hyps)

  let pp     = _pp ~dbg:false
  let pp_dbg = _pp ~dbg:true
      
  let find_opt func hyps =
    let exception Found of Ident.t * hyp in
    try
      Mid.iter (fun id a ->
          if func id a then raise (Found (id,a)) else ()
        ) hyps ;
      None
    with Found (id,a) -> Some (id,a)

  let find_map (func : Ident.t -> hyp -> 'a option) hyps = 
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
    try Mid.find id hyps with
      Not_found -> hyp_error ~loc:None (T.HypUnknown (Ident.to_string id))
  (* the latter case should not happen *)

  let by_name (name : lsymb) hyps =
    match find_opt (fun id _ -> Ident.name id = L.unloc name) hyps with
    | Some (id,f) -> id, f
    | None -> hyp_error ~loc:(Some (L.loc name)) (T.HypUnknown (L.unloc name))

  let filter f hyps = Mid.filter (fun id a -> f id a) hyps
 
  let find_all f hyps = Mid.bindings (filter f hyps)

  let exists f hyps = Mid.exists f hyps

  let is_hyp f hyps = exists (fun _ f' -> f = f') hyps
      
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
        (id :: ids, Mid.add id Hyp.htrue hyps)
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
  let _add ~force id hyp hyps =
    assert (not (Mid.mem id hyps)); 

    if not (is_fresh (Ident.name id) hyps) then
      hyp_error ~loc:None (T.HypAlreadyExists (Ident.name id));

    match find_opt (fun _ hyp' -> hyp = hyp') hyps with
    | Some (id',_) when not force -> id', hyps  
    | _ -> id, Mid.add id hyp hyps


  let add_formula ~force id (h : hyp) (hyps : hyps) =
    let id, hyps = _add ~force id h hyps in
    id, hyps

  let add_i npat f hyps =
    let force, approx, name = match npat with
      | Args.Unnamed  -> true, true, "_"
      | Args.AnyName  -> false, true, Hyp.choose_name f
      | Args.Named s  -> true, false, s
      | Args.Approx s -> true, true, s
    in
    let id = fresh_id ~approx name hyps in

    add_formula ~force id f hyps

  let add npat (f : hyp) hyps : hyps = snd (add_i npat f hyps)

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
  
  let map f hyps  = Mid.map (fun h -> f h) hyps
  let mapi f hyps = Mid.mapi (fun h -> f h) hyps

  let fold func hyps init = Mid.fold func hyps init

  let clear_triv hyps = hyps
end

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
    let _pp_hyp    = Equiv.Any._pp
    let pp_hyp_dbg = Equiv.Any.pp_dbg

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
  TraceHyps.fold (fun _ f acc ->
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
