open Utils

include SystemExprSyntax

(*------------------------------------------------------------------*)
(** {2 General operations} *)

(*------------------------------------------------------------------*)
let subset (type a) table (e1 : a expr) (e2 : a expr) : bool =
  match (e1 :> exposed).cnt, (e2 :> exposed).cnt with
  | Var v1, Var v2 -> Var.equal v1 v2
    
  | Any { compatible_with = s1; pair = p1; }, 
    Any { compatible_with = s2; pair = p2; } ->
    (
      match s1, s2 with
      | None,   Some _ -> false
      | None,   None
      | Some _, None   -> true
      | Some s1, Some s2 -> System.compatible table s1 s2 
    ) 
    && 
    (not p2 || p1)              (* p2 ⇒ p1 *)
      
  | List l, Any { compatible_with = Some s; pair = p; } ->
    ( l = [] || System.compatible table (Stdlib.snd (List.hd l)).system s ) &&
    (not p || List.length l = 2)
      
  | List l1, List l2 ->
    List.for_all (fun s1 -> List.exists (fun s2 -> s1 = s2) l2) l1
      
  | _, Any {compatible_with = None; } -> true
  | _ -> false

let equal (type a) table (e1 : a expr) (e2 : a expr) : bool =
  subset table e1 e2 && subset table e2 e1

(*------------------------------------------------------------------*)
let subset_modulo (type a) table (e1 : a expr) (e2 : a expr) : bool =
  match (e1 :> exposed).cnt, (e2 :> exposed).cnt with
  | List l1, List l2 ->
    List.for_all (fun (_,s1) -> List.exists (fun (_,s2) -> s1 = s2) l2) l1

  | _ -> subset table e1 e2

let equal_modulo (type a) table (e1 : a expr) (e2 : a expr) : bool =
  subset_modulo table e1 e2 && subset_modulo table e2 e1

(*------------------------------------------------------------------*)
(** Get system that is compatible with all systems of an expresion. *)
let get_compatible_sys (type a) (se : a expr) : Symbols.system option = 
  match (se :> exposed).cnt with
  | Var _ | Any { compatible_with = None; } -> None
  | Any { compatible_with = s; } -> s
  | List ((_,s)::_) -> Some s.Single.system
  | List [] -> None

(** Check that all systems in [e1] are compatible with all systems in [e2]. *)
let compatible table (e1 : 'a expr) (e2 : 'b expr) =
  match get_compatible_sys e1, get_compatible_sys e2 with
    | Some s1, Some s2 -> System.compatible table s1 s2
    | None, None -> true
    | _ -> false


(*------------------------------------------------------------------*)
(** {2 Operations on finite sets} *)

let of_system table (s : Symbols.system) : 'a expr =
  let projections = System.projections table s in
  let l = List.map (fun proj -> proj, System.Single.make table s proj) projections in
  let name = Some (Symbols.path_to_string s) in
  force { name; cnt = List l; }

(*------------------------------------------------------------------*)
(* create the bi-system for the empty system declared in the [Prelude] *)
let empty_system table : pair =
  of_system table (Symbols.System.of_string Symbols.top_npath "Empty")

(*------------------------------------------------------------------*)
let default_labels : int -> Projection.t list = function
  | 1 -> [Projection.from_string "ε"]
  | 2 -> [Projection.left; Projection.right]
  | n -> List.init n (fun i -> Projection.from_string (string_of_int (i+1)))

let make_fset ?loc table ~labels (l : Single.t list) : fset =
  (* Check for compatibility. *)
  let () = match l with
    | [] -> ()
    | { Single.system = hd_system } :: tl ->
      List.iter
        (fun {Single.system} ->
           if not (System.compatible table hd_system system) then
             error ?loc Incompatible_systems)
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
  force { name = None; cnt = List (List.combine labels l); }


(*------------------------------------------------------------------*)
(** {2 Action symbols and terms} *)

let symbs (type a) (table : Symbols.table) (se : a expr) = 
  match (se :> exposed).cnt with
  | List ((_,{ system })::_) -> System.symbs table system
  | _ -> assert false

let action_to_term table system a =
  let msymbs = symbs table system in
  let symb = System.Msh.find (Action.get_shape a) msymbs in
  Term.mk_action symb (Action.get_args a)

(*------------------------------------------------------------------*)
(** {2 Action descriptions} *)

(** Compute action description of some system expression for a given shape. *)
let descr_of_shape
    (type a) (table : Symbols.table) (expr : a expr) (shape : Action.shape)
    : Action.descr
  =
  let expr = to_list (to_fset expr) in
  (* TODO refreshing in descr_of_shape useless before combine_descrs *)
  Action.combine_descrs
    (List.map
       (fun (lbl,sys) -> lbl, System.Single.descr_of_shape table sys shape)
       expr)

let descr_of_action
    (table : Symbols.table) expr (a : Action.action)
  : Action.descr * Term.subst
  =
  let descr = descr_of_shape table expr (Action.get_shape a) in
  Action.check_descr descr;
  let d_indices = descr.indices in
  let a_indices = Action.get_args a in
  let subst =
    List.map2
      (fun v t' -> Term.ESubst (Term.mk_var v, t'))
      d_indices a_indices
  in
  descr, subst

let descrs (type a) table (se : a expr) : Action.descr System.Msh.t =
  let symbs = symbs table se in
  System.Msh.mapi
    (fun shape _ -> descr_of_shape table se shape)
    symbs

(*------------------------------------------------------------------*)

let iter_descrs table system (f : Action.descr -> unit) =
  let f _ a = f a in
  System.Msh.iter f (descrs table system)

let map_descrs
    (type b)
    (f : Action.descr -> 'a)
    (table : Symbols.table) (system : b expr)
  : 'a list
  =
  let m = System.Msh.map f (descrs table system) in
  List.map Stdlib.snd (System.Msh.bindings m)

let actions table (system : _ expr) : 'a list =
  let f Action.{action;name;indices} = (action,name,indices) in
  let m = System.Msh.map f (descrs table system) in
  List.map Stdlib.snd (System.Msh.bindings m)

let fold_descrs (f : Action.descr -> 'a -> 'a) table system init =
  let f _ a = f a in
  System.Msh.fold f (descrs table system) init

(*------------------------------------------------------------------*)
(** {2 Miscelaneous} *)

let get_compatible_of_context table (context : context) : compatible option =
  let expr = (context.set :> exposed) in
  match expr.cnt with
  | Any { compatible_with = None; } -> None
  | Any { compatible_with = Some s; } -> 
    let single = System.Single.make table s (Projection.from_string "ε") in
    Some (singleton single :> compatible)
  | _ -> Some (force expr :> compatible)

(*------------------------------------------------------------------*)
let get_compatible_fset table (se : compatible) : fset =
  match (se :> exposed).cnt with
  | Var _ | Any { compatible_with = None; } -> assert false

  | Any { compatible_with = Some s; } -> of_system table s

  | List _ -> force0 se

(*------------------------------------------------------------------*)
let gsubst (type a) (s : Subst.t) (g : a expr) : a expr =
  match (g :> exposed).cnt with
  | Var v -> force0 (Subst.subst_se_var s v)
  | Any _ | List _ -> g

let gsubst_context (s : Subst.t) (g : context) : context =
  { set = gsubst s g.set; pair = omap (gsubst s) g.pair ;}

(*------------------------------------------------------------------*)
(** {2 Pretty-printers} *)
    
let pp_descrs (table : Symbols.table) ppf (system : _) =
  Fmt.pf ppf "@[<v 2>Available actions:@;@;";
  iter_descrs table system (fun descr ->
    Fmt.pf ppf "@[<v 0>@[%a@]@;@]@;"
      (Action.pp_descr table) descr) ;
  Fmt.pf ppf "@]%!@."

let print_system (table : Symbols.table) (system : _ expr) : unit =
  try
  let system = to_fset system in
    Printer.prt `Result "@[<v>System @[[%a]@]@;@[%a@]@]%!"
      pp system
      (pp_descrs table) system
  with Error (_,Expected_fset) ->
    Printer.prt `Result "@[No action descriptions for system %a@]%!"
      pp system

(*------------------------------------------------------------------*)
(** {2 Parsing} *)

module Parse = struct
  type item = {
    system     : Symbols.p_path;
    projection : Symbols.lsymb option;
    alias      : Symbols.lsymb option
  }

  type t = item list L.located

  let parse_system
      ?(se_env = Var.empty_env)
      (table : Symbols.table)
      (system : Symbols.p_path)
    :
      'a expr
    =
    let top, sub = system in
    if top = [] then
      match Var.lookup_string (L.unloc sub) se_env with
      | Some v -> var v
      | None ->
        of_system table (System.convert table system)
    else
      of_system table (System.convert table system)
      
  let parse_single table item =
    assert (item.alias = None);
    
    let sys = System.convert table item.system in
    match item.projection with
    | None ->
      begin match System.projections table sys with
        | [p] -> System.Single.make table sys p
        | _ -> error Missing_projection
      end
    | Some p ->
      System.Single.make table sys (Projection.from_string (L.unloc p))

  let parse ~(se_env : Var.env) table (p : t) : arbitrary = 
    match L.unloc p with
    | [] ->
      (* Default system annotation. *)
      of_system table
        (System.convert table ([], L.mk_loc L._dummy "default"))

    | [{ system = [], { pl_desc = ("any" | "any_pair") as pair}; 
         projection; 
         alias = None}] ->
      let pair = pair = "any_pair" in
      let compatible_with = 
        omap (fun system -> System.convert table ([], system)) projection
      in
      any ~compatible_with ~pair

    | [{ system; projection = None; alias = None}] ->
      parse_system ~se_env table system

    | l ->
      let labels =
        List.map (fun i ->
            Utils.omap (Projection.from_string -| L.unloc) i.alias
          ) l 
      in
      let l =
        List.map (fun i -> parse_single table { i with alias = None }) l
      in
      (make_fset ~loc:(L.loc p) table ~labels l :> arbitrary)

  let parse_pair ~se_env table (c : t) : pair =
    let pair = parse ~se_env table c in
    if not (is_pair ~se_env pair) then error ~loc:(L.loc c) Expected_pair;
    to_pair pair

  (*------------------------------------------------------------------*)
  type p_context_i =
    | NoSystem
    | System   of t
    | Set_pair of t * t

  type p_context = p_context_i L.located 

  type sys = [`Local | `Global] * (p_bnds * p_context)

  (*------------------------------------------------------------------*)
  let empty = L.(mk_loc _dummy [])

  (** Parse the system context for a local statement. *)
  let parse_local_context ~se_env table (c : p_context) : context = 
    match L.unloc c with
    | NoSystem ->
      { set = parse ~se_env table empty ; pair = None }

    | System s ->
      let set = parse ~se_env table s in
      { set ; pair = None }
      
    | Set_pair (s,p) ->
      let set  = parse      ~se_env table s in
      let pair = parse_pair ~se_env table p in
      { set ; pair = Some pair; }

  (** Parse the system context for a global statement. *)
  let parse_global_context ~se_env table (c : p_context) : context = 
    let check_compatible set pair =
      if not (compatible table set pair) then 
        error ~loc:(L.loc c) Incompatible_systems;
    in

    let set, pair =
      match L.unloc c with
      | NoSystem       -> empty, empty
      | System s       -> s, s
      | Set_pair (s,p) -> s, p
    in
    let set  = parse      ~se_env table set in
    let pair = parse_pair ~se_env table pair in
    check_compatible set pair;
    { set ; pair = Some pair; }
end
