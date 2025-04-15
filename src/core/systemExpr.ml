open Utils

include SystemExprSyntax

(*------------------------------------------------------------------*)
(** {2 General operations} *)

(*------------------------------------------------------------------*)
let subset (type a b) _table (e1 : a expr) (e2 : b expr) : bool =
  match (e1 :> exposed).cnt, (e2 :> exposed).cnt with
  | Var v1, Var v2 -> Var.equal v1 v2
    
  | Any, Any -> true
      
  | List l1, List l2 ->
    List.for_all (fun s1 -> List.exists (fun s2 -> s1 = s2) l2) l1
      
  | _, Any -> true
  | _ -> false

let equal (type a b) table (e1 : a expr) (e2 : b expr) : bool =
  subset table e1 e2 && subset table e2 e1

(*------------------------------------------------------------------*)
let subset_modulo (type a b) table (e1 : a expr) (e2 : b expr) : bool =
  match (e1 :> exposed).cnt, (e2 :> exposed).cnt with
  | List l1, List l2 ->
    List.for_all (fun (_,s1) -> List.exists (fun (_,s2) -> s1 = s2) l2) l1

  | _ -> subset table e1 e2

let equal_modulo (type a b) table (e1 : a expr) (e2 : b expr) : bool =
  subset_modulo table e1 e2 && subset_modulo table e2 e1

(*------------------------------------------------------------------*)
(** {2 Operations on finite sets} *)

let of_system table (s : Symbols.system) : 'a expr =
  let projections = System.projections table s in
  let l = List.map (fun proj -> proj, System.Single.make table s proj) projections in
  let name = Some (Symbols.path_to_string s) in
  force { name; cnt = List l; }

(*------------------------------------------------------------------*)
(** path to the empty bi-system declared in the [Prelude] *)
let path_empty : Symbols.system =
  Symbols.System.of_string Symbols.top_npath "Empty"

(** the bi-system for the empty system (in the [Prelude]) *)
let pair_empty table : pair = of_system table path_empty

(** A k-system where all fiels are [Empty/left] (the choice of `left`
    vs `right` is arbitrary). *)
let fset_empty ~(k:int) table : fset =
  let proj = Projection.left in
  let l =
    List.init k (fun _i -> proj, System.Single.make table path_empty proj)
  in
  let name = Some (Symbols.path_to_string path_empty) in
  force { name; cnt = List l; }

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

let get_compatible_of_context table (env : env) (context : context) : compatible option =
  match get_compatible_system env context.set with
  | Some e -> Some (force0 (of_system table e))
  | None -> None

(*------------------------------------------------------------------*)
let gsubst (type a) (s : Subst.t) (g : a expr) : a expr =
  match (g :> exposed).cnt with
  | Var v -> force0 (Subst.subst_se_var s v)
  | Any | List _ -> g

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
      ~(implicit : bool)
      ?(implicit_infos : Var.info list = [])
      (table : Symbols.table) (se_env : env) (system : Symbols.p_path)
    : env * 'a expr
    =
    let top, sub = system in
    let sub = L.unloc sub in
    
    if top = [] then
      match lookup_string sub se_env with
      (* retrieve an existing variable *)
      | Some v -> (se_env, var v)

      (* declare a new variable *)
      | None when implicit && String.starts_with ~prefix:"'" sub ->
        let v = Var.of_ident (Ident.create sub) in
        ( se_env @ [v, implicit_infos], var v)

      (* parse a concrete systeme expression *)
      | None ->
        (se_env, of_system table (System.convert table system))

    else
      (* parse a concrete systeme expression *)
      (se_env, of_system table (System.convert table system))
      
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

  let parse ~implicit ?implicit_infos ~(se_env : env) table (p : t) : env * arbitrary = 
    match L.unloc p with
    | [] ->
      (* Default system annotation. *)
      let s =
        of_system table
          (System.convert table ([], L.mk_loc L._dummy "default"))
      in
      (se_env, s)

    | [{ system; projection = None; alias = None}] ->
      parse_system ~implicit ?implicit_infos table se_env system

    | l ->
      let labels =
        List.map (fun i ->
            Utils.omap (Projection.from_string -| L.unloc) i.alias
          ) l 
      in
      let l =
        List.map (fun i -> parse_single table { i with alias = None }) l
      in
      let s = (make_fset ~loc:(L.loc p) table ~labels l :> arbitrary) in
      (se_env, s)

  let parse_pair ~implicit ~se_env table (c : t) : env * pair =
    let se_env, pair = 
      parse ~implicit ~implicit_infos:[Var.Pair] ~se_env table c 
    in
    if not (is_pair ~se_env pair) then error ~loc:(L.loc c) Expected_pair;
    (se_env, to_pair pair)

  (*------------------------------------------------------------------*)
  type p_context_i =
    | NoSystem
    | System   of t
    | Set_pair of t * t option

  type p_context = p_context_i L.located 

  type sys = [`Local | `Global] * p_context

  (*------------------------------------------------------------------*)
  let empty = L.(mk_loc _dummy [])

  let check_compatible loc table se_env set pair =
    if not (compatible table se_env set pair) then 
      error ~loc Incompatible_systems

  (** Parse the `any` syntactic sugar as a system context. *)
  let parse_any
      ~mode ~se_env table
      (compatible_with : Symbols.lsymb option)
    : env * context
    =
    let compatible_with =
      omap_dflt [] 
        (fun s -> 
           let s = System.convert table ([],s) in
           [Var.Compatible_with s])
        compatible_with
    in
    let p = fresh_var ~prefix:"'P" se_env in
    let q = fresh_var ~prefix:"'Q" se_env in

    let p_infos = compatible_with in
    let q_infos = Var.Pair :: compatible_with in

    match mode with
    | `Local ->
      let se_env = se_env @ [(p, p_infos)] in
      (se_env, { set = var p; pair = None; })

    | `Global ->
      let se_env = se_env @ [(p, p_infos); (q, q_infos) ] in
      (se_env, { set = var p; pair = Some (to_pair (var q)); })

  (** Parse a [set; pair] system context. *)
  let parse_set_pair ~loc ~implicit ~se_env table ~set ~pair =
    let se_env, set  = parse ~implicit ~se_env table set in
    let se_env, pair =
      omap_dflt
        (se_env, None)
        ( snd_bind some -|
          parse_pair ~implicit ~se_env table )
        pair
    in

    if pair <> None then
      check_compatible loc table se_env set (oget pair);

    se_env, { set ; pair; }

  (** Parse the system context for a local statement. *)
  let parse_local_context
      ~implicit ~se_env table (c : p_context)
    : env * context
    =
    let loc = L.loc c in
    let parse_set_pair = parse_set_pair ~loc ~implicit ~se_env table in
    match L.unloc c with
    | System                   (* [c = any] *)
        { pl_loc;
          pl_desc = [{ system = ([], { pl_desc = "any"}); 
                       projection = p; 
                       alias = None}] } ->
      if not implicit then 
        error ~loc:pl_loc (Failure "implicit unsupported");

      parse_any ~mode:`Local ~se_env table p

    | NoSystem       -> parse_set_pair ~set:empty ~pair:None
    | System s       -> parse_set_pair ~set:s     ~pair:None
    | Set_pair (s,p) -> parse_set_pair ~set:s     ~pair:p

  (** Parse the system context for a global statement. *)
  let parse_global_context
      ~implicit ~se_env table (c : p_context)
    : env * context
    =
    let loc = L.loc c in
    let parse_set_pair = parse_set_pair ~loc ~implicit ~se_env table in
    match L.unloc c with
    | System                    (* [c = any] *)
        { pl_loc;
          pl_desc = [{ system = ([], { pl_desc = "any"}); 
                       projection = p; 
                       alias = None}] } ->
      if not implicit then 
        error ~loc:pl_loc (Failure "implicit unsupported");

      parse_any ~mode:`Global ~se_env table p

    | NoSystem       -> parse_set_pair ~set:empty ~pair:(Some empty)
    | System s       -> parse_set_pair ~set:s     ~pair:(Some s)
    | Set_pair (s,p) -> parse_set_pair ~set:s     ~pair:p
end
