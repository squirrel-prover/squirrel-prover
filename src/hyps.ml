(*------------------------------------------------------------------*)  
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
module type Hyp =sig 
  type t 
  val pp_hyp : Format.formatter -> t -> unit
  val htrue : t
end

(*------------------------------------------------------------------*) 
module type S = sig
  type hyp 

  type ldecl = Ident.t * hyp

  type hyps

  val empty : hyps

  val is_hyp : hyp -> hyps -> bool
    
  val by_id   : Ident.t -> hyps -> hyp
  val by_name : string  -> hyps -> ldecl

  val hyp_by_name : string  -> hyps -> hyp
  val id_by_name  : string  -> hyps -> Ident.t

  val fresh_id : string -> hyps -> Ident.t
  val fresh_ids : string list -> hyps -> Ident.t list
  
  val add : force:bool -> Ident.t -> hyp -> hyps -> Ident.t * hyps

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

  val fold : (Ident.t -> hyp -> 'a -> 'a) -> hyps -> 'a -> 'a
    
  val pp_ldecl : ?dbg:bool -> Format.formatter -> ldecl -> unit
  val pps : ?dbg:bool -> Format.formatter -> hyps -> unit
end


(*------------------------------------------------------------------*)
module Mk (Hyp : Hyp) : S with type hyp = Hyp.t = struct 
  module Mid = Ident.Mid

  type hyp = Hyp.t
  type ldecl = Ident.t * hyp

  (* We are using maps from idents to hypothesis, though we do not exploit
     much that map structure. *)
  type hyps = hyp Mid.t
  
  let empty =  Mid.empty

  let pp_ldecl ?(dbg=false) ppf (id,hyp) =
    Fmt.pf ppf "%a: %a@;"
      (if dbg then Ident.pp_full else Ident.pp) id
      Hyp.pp_hyp hyp

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

  let fresh_ids names (hyps : hyps) =
    let ids, _ = List.fold_left (fun (ids,hyps) name ->
        let id = fresh_id name hyps in
        (* We add the id to [hyps] to reserve the name *)
        (id :: ids, Mid.add id Hyp.htrue hyps)
      ) ([], hyps) names in
    List.rev ids
    
  let add ~force id hyp hyps =
    assert (not (Mid.mem id hyps)); 

    if not (is_fresh (Ident.name id) hyps) then
      hyp_error (HypAlreadyExists (Ident.name id));

    match find_opt (fun _ hyp' -> hyp = hyp') hyps with
    | Some (id',_) when not force -> id', hyps  
    | _ -> id, Mid.add id hyp hyps
  
  let mem_id id hyps = Mid.mem id hyps
  let mem_name name hyps =
    Mid.exists (fun id' _ -> Ident.name id' = name) hyps
  
  let map f hyps = Mid.map (fun h -> f h) hyps

  let fold func hyps init = Mid.fold func hyps init 
end
