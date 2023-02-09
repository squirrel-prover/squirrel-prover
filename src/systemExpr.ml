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

let is_any_or_any_comp : t -> bool = function
  | Any | Any_compatible_with _ -> true
  | _ -> false

(*------------------------------------------------------------------*)
let pp fmt : 'a expr -> unit = function
  | Any -> Format.fprintf fmt "any"
  | Any_compatible_with s -> Format.fprintf fmt "any/%a" Symbols.pp s
  | List l ->
      Fmt.list
        ~sep:Fmt.comma
        (fun fmt (label,single_sys) ->
           if Term.proj_to_string label = "ε" then
             System.Single.pp fmt single_sys
           else
             Format.fprintf fmt "%a:%a"
               Term.pp_proj label
               System.Single.pp single_sys)
        fmt
        l

(*------------------------------------------------------------------*)
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

(*------------------------------------------------------------------*)
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
let equal table s1 s2 = subset table s1 s2 && subset table s2 s1

(*------------------------------------------------------------------*)
(** Get system that is compatible with all systems of an expresion. *)
let get_compatible_sys = function
  | Any -> None
  | Any_compatible_with s -> Some s
  | List ((_,s)::_) -> Some s.System.Single.system
  | List [] -> assert false

(** Check that all systems in [e1] are compatible with all systems in [e2]. *)
let compatible table e1 e2 =
  match get_compatible_sys e1, get_compatible_sys e2 with
    | Some s1, Some s2 -> System.compatible table s1 s2
    | _ -> false

(*------------------------------------------------------------------*)
(** {2 Finite sets} *)

let to_list = function
  | List l -> l
  | _ -> assert false

let of_list l = List l

let to_projs t = List.map fst (to_list t)

(*------------------------------------------------------------------*)    
let to_list_any (t : _ expr) : (Term.proj * System.Single.t) list option =
  match t with
  | List l -> Some l
  | Any | Any_compatible_with _ -> None

let to_projs_any (t : _ expr) : Term.projs option =
  match t with
  | List l -> Some (List.map fst l)
  | Any | Any_compatible_with _ -> None

(*------------------------------------------------------------------*)
let project_opt (projs : Term.projs option) (t : fset) : fset =
  match t, projs with
  | List l, Some projs ->
    (* we only project over a subset of [l]'s projs *)
    assert (List.for_all (fun x -> List.mem_assoc x l) projs);

    List (List.filter (fun (x,_) -> List.mem x projs) l)

  | (Any | Any_compatible_with _), Some _projs -> assert false
  (* should this be [List projs] ? *)

  | _, None -> t
    
let project (projs : Term.projs) t = project_opt (Some projs) t

(*------------------------------------------------------------------*)  
let singleton s = List [Term.proj_from_string "ε",s]

let of_system table s : t =
  let projections = System.projections table s in
  List
    (List.map (fun proj -> proj, System.Single.make table s proj) projections)

(*------------------------------------------------------------------*)
let default_labels : int -> Term.proj list = function
  | 1 -> [Term.proj_from_string "ε"]
  | 2 -> [Term.left_proj;Term.right_proj]
  | n -> List.init n (fun i -> Term.proj_from_string (string_of_int (i+1)))

(*------------------------------------------------------------------*)
let make_fset table ~labels (l : System.Single.t list) : t =
  (* Check for compatibility. *)
  let () = match l with
    | [] -> assert false
    | { System.Single.system = hd_system } :: tl ->
      List.iter
        (fun {System.Single.system} ->
           if not (System.compatible table hd_system system) then
             error Incompatible_systems)
        tl
  in
  (* Build labelled list using a mix of default and provided labels. *)
  let len = List.length l in
  assert (List.length labels = len);

  let labels =
    List.map2 (fun default -> function
        | None -> default
        | Some x -> x
      )
      (default_labels len)
      labels
  in
  List (List.combine labels l)

(*------------------------------------------------------------------*)
(** Action symbols and terms *)

let symbs table = function
  | List ((_,{System.Single.system})::_) -> System.symbs table system
  | _ -> assert false

let action_to_term table system a =
  let msymbs = symbs table system in
  let symb = System.Msh.find (Action.get_shape a) msymbs in
  Term.mk_action symb (Action.get_args a)

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

let descr_of_action table expr (a : Action.action) : Action.descr * Term.subst =
  let descr = descr_of_shape table expr (Action.get_shape a) in
  assert (Action.check_descr descr);
  let d_indices = descr.indices in
  let a_indices = Action.get_args a in
  let subst =
    List.map2
      (fun v t' -> Term.ESubst (Term.mk_var v, t'))
      d_indices a_indices
  in
  descr, subst

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
(* Pairs *)

let make_pair a b = List [Term.left_proj,a; Term.right_proj,b]

let fst = function
  | List [x;_] -> x
  | _ -> assert false

let snd = function
  | List [_;x] -> x
  | _ -> assert false

(*------------------------------------------------------------------*)
(** {2 Contexts} *)

type context = {
  set  : arbitrary expr ;
  pair : pair expr option
}

let context_any = { set = any ; pair = None }

let equivalence_context ?set pair =
  let set = match set with
    | Some s -> s
    | None ->
       begin match pair with
         | List ((_,ss)::_) -> any_compatible_with ss.system
         | _ -> assert false
       end
  in
  { pair = Some pair ; set }

let reachability_context set = { set ; pair = None }

let pp_context fmt = function
  | { set; pair = None   } -> pp fmt set
  | { set; pair = Some p } ->
      if set = p then
        Format.fprintf fmt "%a@ (same for equivalences)" pp set
      else
        Format.fprintf fmt "%a@ (@[<2>equivalences:@ %a@])" pp set pp p

let pp_context fmt c = Format.fprintf fmt "@[%a@]" pp_context c

let get_compatible_expr = function
  | { set = Any } -> None
  | { set = expr } -> Some expr

let project_set (projs : Term.projs) (c : context) : context =
  { c with set = project projs c.set }

let project_set_opt (projs : Term.projs option) (c : context) : context =
  { c with set = project_opt projs c.set }


(*------------------------------------------------------------------*)
(** Cf `.mli` *)
let mk_proj_subst
    ~strict
    ~(src: t) ~(dst: t)
  : Term.projs option * (Term.proj * Term.proj) list
  =
  let psubst : (Term.proj * Term.proj) list option = 
    if is_any_or_any_comp dst || is_any_or_any_comp src then
      None

    else begin
      let dst = to_list (to_fset dst) in
      (* [src] may not apply to all systems in [dst] *)
      let src_systems = to_list (to_fset src) in

      if dst = src_systems then None else
        (* [l] contains tuples [(p,q), single] where:
           - [p] is a projection of [src] for [single]
           - [q] is a projection of [dst] for [single] *)
        let l =
          List.filter_map (fun (p, single) ->
              let res =
                List.find_map (fun (p_src, src_single) -> 
                    if single = src_single then
                      Some ((p_src,p), single)
                    else None
                  ) src_systems
              in
              if strict then assert (res <> None);
              res
            ) dst
        in

        (* If two projections of [src] applies to the
           same element in [dst], there is an ambiguity
           about which rewriting to apply.
           In that case, we raise an error. *)
        if List.exists (fun ((p_src, p), single) ->
            List.exists (fun ((p_src', p'), single') ->
                p_src <> p_src' && p = p' && single = single'
              ) l
          ) l then
          Printer.prt `Warning "system projection ambiguity";

        Some (List.map Stdlib.fst l)
    end
  in

  let projs = omap (List.map Stdlib.snd) psubst in
  let psubst = odflt [] psubst in

  projs, psubst

(*------------------------------------------------------------------*)
(** {2 Misc} *)
  
let print_system (table : Symbols.table) (system : _ expr) : unit =
  try
  let system = to_fset system in
    Printer.prt `Result "@[<v>System @[[%a]@]@;@[%a@]@]%!"
      pp system
      (pp_descrs table) system
  with Error Expected_fset ->
    Printer.prt `Result "@[No action descriptions for system %a@]%!"
      pp system

(*------------------------------------------------------------------*)
let is_single_system (se : context) : bool =
  if not (is_fset se.set) then false
  else
    let pair_fsets =
      match se.pair with
      | None -> []
      | Some pair ->
        [Stdlib.snd (fst pair); Stdlib.snd (snd pair)]
    in
    let set_fsets = List.map Stdlib.snd (to_list (to_fset se.set)) in
    let fsets = pair_fsets @ set_fsets in
    let single = List.hd fsets in
    List.for_all (fun single' -> single = single') fsets

(*------------------------------------------------------------------*)
(** {2 Parsing} *)

module Parse = struct
  type item = {
    system     : Symbols.lsymb;
    projection : Symbols.lsymb option;
    alias      : Symbols.lsymb option
  }

  type t = item list L.located

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

  let parse table p = match L.unloc p with
    | [] ->
      (* Default system annotation. We might make it mean "any" eventually
         but for now "default" avoids changing most files. *)
      of_system table
        (System.of_lsymb table (L.mk_loc L._dummy "default"))

    | [{ system = { pl_desc = "any" }; projection = None; alias = None}] ->
      any

    | [{ system = { pl_desc = "any" }; projection = Some system}] ->
      any_compatible_with (System.of_lsymb table system)

    | [{ system; projection = None; alias = None}] ->
      of_system table (System.of_lsymb table system)

    | l ->
      let labels =
        List.map (fun i ->
            Utils.omap (Term.proj_from_string -| L.unloc) i.alias
          ) l 
      in
      let l =
        List.map (fun i -> parse_single table { i with alias = None }) l
      in
      make_fset table ~labels l

  (*------------------------------------------------------------------*)
  type sys_cnt =
    | NoSystem
    | System   of t
    | Set_pair of t * t

  type sys = [`Local | `Global] * sys_cnt

  (*------------------------------------------------------------------*)
  let empty = L.(mk_loc _dummy [])

  let parse_local_context table : sys_cnt -> context = function
    | NoSystem ->
      { set = parse table empty ; pair = None }
    | System s ->
      let set = parse table s in
      { set ; pair = None }
    | Set_pair (s,p) ->
      let set = parse table s in
      let pair = Some (to_pair (parse table p)) in
      { set ; pair }

  let parse_global_context table : sys_cnt -> context = function
    | NoSystem ->
      let set = parse table empty in
      let pair = to_pair set in
      { set ; pair = Some pair }
    | System s ->
      let set = parse table s in
      let pair = to_pair set in
      { set ; pair = Some pair }
    | Set_pair (s,p) ->
      let set = parse table s in
      let pair = Some (to_pair (parse table p)) in
      { set ; pair }

  let parse_sys table ((k,p_system) : sys) : context =
    match k with
    | `Local  -> parse_local_context  table p_system
    | `Global -> parse_global_context table p_system
end
