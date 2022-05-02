open Utils
module L = Location

type error =
  | Invalid_projection
  | Missing_projection
  | Incompatible_systems
  | Expected_compatible
  | Expected_fset
  | Expected_pair

exception Error of error

let error e = raise (Error e)

let pp_error fmt = function
  | Invalid_projection -> Format.fprintf fmt "invalid projection"
  | Missing_projection -> Format.fprintf fmt "missing projection"
  | Incompatible_systems -> Format.fprintf fmt "incompatible systems"
  | Expected_compatible -> Format.fprintf fmt "expected a compatible expr"
  | Expected_fset -> Format.fprintf fmt "expected a finite set expr"
  | Expected_pair -> Format.fprintf fmt "expected a pair expr"

(*------------------------------------------------------------------*)
(** {2 Expressions} *)

type t =
  | Any
  | Any_compatible_with of System.t
  | List of (Term.proj * System.Single.t) list
      (** Each single system is identified by a label.
          The list cannot be empty. All single systems are compatible. *)

type 'a expr = t

type arbitrary  = < > expr
type compatible = < symbols : unit > expr
type fset       = < symbols : unit ; fset : unit > expr
type pair       = < symbols : unit ; fset : unit ; pair : unit > expr

type equiv_t = pair expr

(*------------------------------------------------------------------*)
let hash : 'a expr -> int = Hashtbl.hash

(*------------------------------------------------------------------*)
let any = Any

let any_compatible_with s = Any_compatible_with s

(*------------------------------------------------------------------*)
let is_fset : t -> bool = function List _ -> true | _ -> false

(*------------------------------------------------------------------*)
let pp fmt : 'a expr -> unit = function
  | Any -> Format.fprintf fmt "any"
  | Any_compatible_with s -> Format.fprintf fmt "any(%a)" Symbols.pp s
  | List l ->
      Fmt.list
        ~sep:Fmt.comma
        (fun fmt (label,single_sys) ->
           if Term.proj_to_string label = "" then
             System.Single.pp fmt single_sys
           else
             Format.fprintf fmt "%a:%a"
               Term.pp_proj label
               System.Single.pp single_sys)
        fmt
        l

let to_arbitrary : type a. a expr -> arbitrary expr = fun x -> x

let to_compatible = function
  | Any -> error Expected_compatible
  | x -> x

let to_fset = function
  | List _ as x -> x
  | _ -> error Expected_fset

let to_pair = function
  | List [_;_] as x -> x
  | _ -> error Expected_pair

let subset table e1 e2 = match e1,e2 with
  | Any_compatible_with s1, Any_compatible_with s2 ->
    System.compatible table s1 s2
      
  | List l, Any_compatible_with s ->
    System.compatible table (snd (List.hd l)).system s
      
  | List l1, List l2 ->
    List.for_all (fun (_,s1) -> List.exists (fun (_,s2) -> s1 = s2) l2) l1
      
  | _, Any -> true
  | _ -> false

(*------------------------------------------------------------------*)
(** {2 Finite sets} *)

let to_list = function
  | List l -> l
  | _ -> assert false

let project_opt (projs : Term.projs option) t =
  match t, projs with
  | List l, Some projs ->
    (* we only project over a subset of [l]'s projs *)
    assert (List.for_all (fun x -> List.mem_assoc x l) projs);

    List (List.filter (fun (x,_) -> List.mem x projs) l)

  | (Any | Any_compatible_with _), Some projs -> assert false

  | _, None -> t
    
let project  (projs : Term.projs) t = project_opt (Some projs) t
  
let singleton s = List [Term.proj_from_string "",s]

let of_system table s : t =
  let projections = System.projections table s in
  List
    (List.map (fun proj -> proj, System.Single.make table s proj) projections)

let default_labels : int -> Term.proj list = function
  | 1 -> [Term.proj_from_string ""]
  | 2 -> [Term.left_proj;Term.right_proj]
  | n -> List.init n (fun i -> Term.proj_from_string (string_of_int (i+1)))

let of_list table ?labels (l:System.Single.t list) : t =
  (* Check for compatibility. *)
  let {System.Single.system=hd_system},tl = match l with
    | hd::tl -> hd,tl
    | [] -> raise (Invalid_argument "SystemExpr.of_list")
  in
  List.iter
    (fun {System.Single.system} ->
       if not (System.compatible table hd_system system) then
         error Incompatible_systems)
    tl;
  (* Build labelled list using a mix of default and provided labels. *)
  match labels with
    | None ->
        List (List.combine (default_labels (List.length l)) l)
    | Some labels ->
        let len = List.length l in
        if List.length labels <> len then
          raise (Invalid_argument "SystemExpr.of_list");
        let labels =
          List.map2
            (fun default -> function None -> default | Some x -> x)
            (default_labels len)
            labels
        in
        List (List.combine labels l)

(*------------------------------------------------------------------*)
(** {2 Parsing} *)

type parse_item = {
  system     : Symbols.lsymb;
  projection : Symbols.lsymb option;
  alias      : Symbols.lsymb option
}

type parsed_t = parse_item list Location.located

let parse_single table item =
  if item.alias <> None then
    raise (Invalid_argument "SystemExpr.Single.parse");
  let sys = System.of_lsymb table item.system in
  match item.projection with
    | None ->
        begin match System.projections table sys with
          | [p] -> System.Single.make table sys p
          | _ -> error Missing_projection
        end
    | Some p ->
        System.Single.make table sys (Term.proj_from_string (L.unloc p))

let parse table p = match Location.unloc p with
  | [] ->
      (* Default system annotation. We might make it mean "any" eventually
         but for now "default" avoids changing most files. *)
      of_system table
        (System.of_lsymb table (Location.mk_loc Location._dummy "default"))

  | [{system={pl_desc="any"};projection=None;alias=None}] ->
      any

  | [{system={pl_desc="any"};projection=Some system}] ->
      any_compatible_with (System.of_lsymb table system)

  | [{system;projection=None;alias=None}] ->
      of_system table (System.of_lsymb table system)

  | l ->
    let labels =
      List.map (fun i ->
          Utils.omap (Term.proj_from_string -| L.unloc) i.alias
        ) l in
      let l =
        List.map (fun i -> parse_single table { i with alias = None }) l
      in
      of_list table ~labels l

(*------------------------------------------------------------------*)
(** Action symbols and terms *)

let symbs table = function
  | List ((_,{System.Single.system})::_) -> System.symbs table system
  | _ -> assert false

let action_to_term table system a =
  let msymbs = symbs table system in
  let symb = System.Msh.find (Action.get_shape a) msymbs in
  Term.mk_action symb (Action.get_indices a)

(*------------------------------------------------------------------*)
(** Action descriptions *)

(** Compute action description of some system expression for a given shape. *)
let descr_of_shape table expr shape =
  let expr = to_list expr in
  (* TODO refreshing in descr_of_shape useless before combine_descrs *)
  Action.combine_descrs
    (List.map
       (fun (lbl,sys) -> lbl, System.Single.descr_of_shape table sys shape)
       expr)

let descr_of_action table expr a =
  let descr = descr_of_shape table expr (Action.get_shape a) in
  let d_indices = descr.indices in
  let a_indices = Action.get_indices a in
  let subst =
    List.map2
      (fun v v' -> Term.ESubst (Term.mk_var v, Term.mk_var v'))
      d_indices a_indices
  in
  Action.subst_descr subst descr

let descrs table (se:fset expr) : Action.descr System.Msh.t =
  let symbs = symbs table se in
  System.Msh.mapi
    (fun shape _ -> descr_of_shape table se shape)
    symbs

(*------------------------------------------------------------------*)

let iter_descrs table system (f : Action.descr -> unit) =
  let f _ a = f a in
  System.Msh.iter f (descrs table system)

let map_descrs (f : Action.descr -> 'a) table system : 'a list =
  let m = System.Msh.map f (descrs table system) in
  List.map snd (System.Msh.bindings m)

let actions table system : 'a list =
  let f Action.{action;name;indices} = (action,name,indices) in
  let m = System.Msh.map f (descrs table system) in
  List.map snd (System.Msh.bindings m)

let fold_descrs (f : Action.descr -> 'a -> 'a) table system init =
  let f _ a = f a in
  System.Msh.fold f (descrs table system) init

(*------------------------------------------------------------------*)

let pp_descrs (table : Symbols.table) ppf (system : t) =
  Fmt.pf ppf "@[<v 2>Available actions:@;@;";
  iter_descrs table system (fun descr ->
    Fmt.pf ppf "@[<v 0>@[%a@]@;@]@;"
      Action.pp_descr descr) ;
  Fmt.pf ppf "@]%!@."

(*------------------------------------------------------------------*)

let clone_system 
    (table      : Symbols.table)
    (old_system : t)
    (new_system : Symbols.lsymb)
    (map        : Action.descr -> Action.descr)
  : Symbols.table * Symbols.system 
  =
  let projections = List.map fst (to_list old_system) in
  let old_actions = descrs table old_system in
  let table, new_system = System.declare_empty table new_system projections in
  let table =
    System.Msh.fold
      (fun _ descr table ->
         let descr = map descr in
         let table,_,_ = System.register_action table new_system descr in
         table)
      old_actions
      table
  in
  table, new_system

(*------------------------------------------------------------------*)
(* Pairs *)

let make_pair a b = List [Term.left_proj,a; Term.right_proj,b]

let fst = function
  | List [x;_] -> x
  | _ -> assert false

let snd = function
  | List [_;x] -> x
  | _ -> assert false

(*------------------------------------------------------------------*)
(* Contexts *)

type context = {
  set  : arbitrary expr ;
  pair : pair expr option
}

let context_any = { set = any ; pair = None }

let update ?set ?pair ctxt = match set,pair with
  | None, None -> ctxt
  | Some s, Some p -> { set = s ; pair = Some p }
  | Some s, None -> { set = s ; pair = None }
  | None, Some p ->
      let _,{System.Single.system=s} = fst p in
      { set = any_compatible_with s ; pair = Some p }

let pp_context fmt = function
  | {set;pair=None} -> pp fmt set
  | {set;pair=Some p} ->
      assert (set = p) ;
      pp fmt p

let get_compatible_expr = function
  | { set = Any } -> None
  | { set = expr } -> Some expr
