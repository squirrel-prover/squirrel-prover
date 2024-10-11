open Utils

(*------------------------------------------------------------------*)
module L = Location
module Single = SystemSyntax.Single

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type error_i =
  | Invalid_projection
  | Missing_projection
  | Incompatible_systems
  | Expected_compatible
  | Expected_fset
  | Expected_pair

type error = L.t option * error_i

exception Error of error

let error ?loc e = raise (Error (loc,e))

let pp_error_i fmt = function
  | Invalid_projection   -> Fmt.pf fmt "invalid system projection"
  | Missing_projection   -> Fmt.pf fmt "missing system projection"
  | Incompatible_systems -> Fmt.pf fmt "incompatible systems"
  | Expected_compatible  -> Fmt.pf fmt "expected a compatible system expression"
  | Expected_fset        -> Fmt.pf fmt "expected a finite system set expression"
  | Expected_pair        -> Fmt.pf fmt "expected a system expression pair"

let pp_error pp_loc_err_opt fmt (loc,e) =
  Fmt.pf fmt "%aSystem error: %a"
    pp_loc_err_opt loc
    pp_error_i e

(*------------------------------------------------------------------*)
(** {2 System expression variables} *)

module Var = struct
  type t = Ident.t

  type info = Pair

  (*------------------------------------------------------------------*)
  let pp = Ident.pp

  let pp_info fmt = function
    | Pair -> Fmt.pf fmt "pair"

  (*------------------------------------------------------------------*)
  let equal = Ident.equal

  (*------------------------------------------------------------------*)
  let name (t : t) = Ident.name t

  (*------------------------------------------------------------------*)
  let of_ident s = s
  let to_ident s = s

  (*------------------------------------------------------------------*)
  let set  = Ident.create "set"
  let pair = Ident.create "equiv"

  (*------------------------------------------------------------------*)
  (** {3 Sets and maps} *)
      
  module O = struct
    type _t = t
    type t  = _t
    let compare = Ident.compare
  end

  module M = Map.Make (O)
  module S = Set.Make (O)

  (*------------------------------------------------------------------*)
  (** {3 Environment} *)

  type env = info list M.t

  let empty_env : env = M.empty

  let lookup_string (se_name : string) (env : env) : t option =
    (* FIXME: inefficient as we lookup through the whole table *)
    let found = ref None in
    M.iter (fun v' _ ->
        if name v' = se_name then begin
          (* It must be guaranteed that [env.se_vars] does
             not contains multiple identically named
             variables. *)
          assert (!found = None); 
          found := Some v'
        end
      ) env;
    !found

end

(*------------------------------------------------------------------*)
(** A system expression variable with a list of [Var.info]s
    constraining its possible instantiation. *)
type tagged_var = Var.t * Var.info list

type tagged_vars = tagged_var list

let pp_tagged_var fmt (v,infos) =
  if infos = [] then
    Fmt.pf fmt "%a" Var.pp v
  else
    Fmt.pf fmt "%a[@[%a@]]"
      Var.pp v
      (Fmt.list ~sep:(Fmt.any ",@ ") Var.pp_info) infos

let pp_tagged_vars =
  Fmt.list ~sep:(Fmt.any ",@ ") pp_tagged_var

type p_bnd  = (string L.located * string L.located list) 
type p_bnds = p_bnd list

(*------------------------------------------------------------------*)
(** {2 System expressions} *)

type any_info = {
  pair : bool;
  (** if true, restricts to pair of labeled single systems. *)
  compatible_with : Symbols.system option
  (** if [Some s], restricts labeled single systems compatible with [s]. *)
}

type cnt =
  | Var of Var.t
  | Any of any_info
  | List of (Projection.t * Single.t) list
  (** Each single system is identified by a label. Can be empty.
      All single systems are compatible. *)

(** exposed type for system expressions *)
type 'a exposed = {
  cnt  : cnt;
  name : string option;         (** optional short name, for printing *)
}

(** private type for system expressions *)
type 'a expr = 'a exposed

type arbitrary  = < > expr
type compatible = < symbols : unit > expr
type fset       = < symbols : unit ; fset : unit > expr
type pair       = < symbols : unit ; fset : unit ; pair : unit > expr

type t = < > expr

(*------------------------------------------------------------------*)
let hash (x : 'a expr) : int = Hashtbl.hash x.cnt

let mk ?name cnt = { cnt; name; }

(** exported *)
external force  : 'a exposed -> 'b expr = "%identity"
external force0 : 'a expr    -> 'b expr = "%identity"

(*------------------------------------------------------------------*)
(** {2 Substitutions} *)

(*------------------------------------------------------------------*)
let subst_projs (s : (Projection.t * Projection.t) list) (t : 'a expr) : 'a expr =
  match t.cnt with
  | Var _ -> t                  (* FIXME: unclear what should be done here *)
  | Any _ -> t
  | List l ->
    mk (List (List.map (fun (p,single) -> List.assoc_dflt p p s, single) l))

(*------------------------------------------------------------------*)
(** {2 Conversions} *)

(*------------------------------------------------------------------*)
let var v = mk (Var v)

(*------------------------------------------------------------------*)
let any ~compatible_with ~pair = mk (Any {compatible_with; pair; })

let full_any = any ~compatible_with:None ~pair:false

(*------------------------------------------------------------------*)
let is_fset (type a) (se : a expr) : bool =
  match se.cnt with List _ -> true | _ -> false

let is_any (type a) (se : a expr) : bool =
  match se.cnt with
  | Any _ -> true
  | _ -> false

let is_pair (type a) (se : a expr) : bool =
  match se.cnt with
  | Any { pair = true; } -> true
  | List [_;_]           -> true

  | Var _                -> true
  (* FIXME: I broke the interface there I think *)

  | _ -> false

(*------------------------------------------------------------------*)
let pp fmt (se : 'a expr) : unit =
  if se.name <> None then
    Fmt.pf fmt "%s" (oget se.name)
  else
    match se.cnt with
    | Var v -> Fmt.pf fmt "%a" Var.pp v

    | Any {compatible_with; pair; } ->
      let pp_head fmt =
        if pair then Fmt.pf fmt "any_pair" else Fmt.pf fmt "any"
      in
      let pp_tail fmt =
        match compatible_with with
        | None -> ()
        | Some s -> Fmt.pf fmt "/%a" Symbols.pp_path s
      in
      Fmt.pf fmt "%t%t" pp_head pp_tail

    | List l ->
      Fmt.list
        ~sep:Fmt.comma
        (fun fmt (label,single_sys) ->
           if Projection.to_string label = "ε" then
             Single.pp fmt single_sys
           else
             Fmt.pf fmt "%a:%a"
               Projection.pp label
               Single.pp single_sys)
        fmt
        l

(*------------------------------------------------------------------*)
let to_arbitrary (type a) (x : a expr) : arbitrary = force x

let to_compatible (type a) (se : a expr) : compatible =
  match se.cnt with
  | Var _ | Any { compatible_with = None; } -> error Expected_compatible
  | Any { compatible_with = Some _; } | _ -> force se

let to_fset (type a) (se : a expr) : fset =
  if not (is_fset se) then error Expected_fset; (* FIXME: replace by an assert *)
  force se

let to_pair (type a) (se : a expr) : pair =
  assert (is_pair se);
  force se

(*------------------------------------------------------------------*)
let equal0 s1 s2 = s1.cnt = s2.cnt


(*------------------------------------------------------------------*)
(** {2 Finite sets} *)

let to_list se =
  match se.cnt with
  | List l -> l
  | _ -> assert false

let of_list l = mk (List l)

let to_projs (t : _) = List.map fst (to_list t)

(*------------------------------------------------------------------*)
let to_list_any (t : _ expr) : (Projection.t * Single.t) list option =
  match t.cnt with
  | List l -> Some l
  | Var _ | Any _ -> None

let to_projs_any (t : _ expr) : Projection.t list option =
  match t.cnt with
  | List l -> Some (List.map fst l)
  | Var _ | Any _ -> None

(*------------------------------------------------------------------*)
let project_opt (projs : Projection.t list option) (t : 'a expr) =
  match t.cnt, projs with
  | List l, Some projs ->
    (* we only project over a subset of [l]'s projs *)
    assert (List.for_all (fun x -> List.mem_assoc x l) projs);

    mk (List (List.filter (fun (x,_) -> List.mem x projs) l))

  | (Any _ | Var _), Some _projs -> assert false

  | _, None -> t

let project (projs : Projection.t list) t = project_opt (Some projs) t

(*------------------------------------------------------------------*)
let singleton s = mk (List [Projection.from_string "ε",s])

(*------------------------------------------------------------------*)
(* Pairs *)

let make_pair
    ((l,a) : Projection.t * Single.t)
    ((r,b) : Projection.t * Single.t)
  =
  mk (List [l,a; r,b])

let fst se =
  match se.cnt with
  | List [x;_] -> x
  | _ -> assert false

let snd se =
  match se.cnt with
  | List [_;x] -> x
  | _ -> assert false

(*------------------------------------------------------------------*)
(** {2 Contexts} *)

type context = {
  set  : arbitrary ;
  pair : pair option
}

let context_any =
  { set  = any ~compatible_with:None ~pair:false ;
    pair = None;
  }

let equal_context0 c c' =
  equal0 c.set c'.set &&
  oequal equal0 c.pair c'.pair

let equivalence_context ?set pair =
  let set = match set with
    | Some s -> s
    | None ->
      begin match pair.cnt with
        | List ((_,ss)::_) -> any ~compatible_with:(Some ss.system) ~pair:false
        | _ -> assert false
      end
  in
  let set, pair = force set, force pair in
  { pair = Some pair ; set }

let reachability_context set = { set = force set ; pair = None }

let pp_context fmt = function
  | { set; pair = None   } -> pp fmt set
  | { set; pair = Some p } ->
      if set.cnt = p.cnt then
        Fmt.pf fmt "%a@ (same for equivalences)" pp set
      else
        Fmt.pf fmt "%a@ (@[<2>equivalences:@ %a@])" pp set pp p

let pp_context fmt c = Fmt.pf fmt "@[%a@]" pp_context c

let project_set (projs : Projection.t list) (c : context) : context =
  { c with set = project projs c.set }

let project_set_opt (projs : Projection.t list option) (c : context) : context =
  { c with set = project_opt projs c.set }


(*------------------------------------------------------------------*)
(** Cf `.mli` *)
let mk_proj_subst
    ~strict
    ~(src: t) ~(dst: t)
  : Projection.t list option * (Projection.t * Projection.t) list
  =
  match dst.cnt, src.cnt with
  | (Any _), _ | _, (Any _) -> None, []

  | Var _, _ | _, Var _ -> assert false (* only concrete systems are supported *)

  | List dst, List src ->
    (* [src] may not apply to all systems in [dst] *)

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
                ) src
            in
            if strict then assert (res <> None);
            res
          ) dst
      in

      (* If two projections of [src] apply to the
         same element in [dst], there is an ambiguity
         about which rewriting to apply.
         In that case, we issue a warning. *)
      if List.exists (fun ((p_src, p), single) ->
          List.exists (fun ((p_src', p'), single') ->
              p_src <> p_src' && p = p' && single = single'
            ) l
        ) l then
        Printer.prt `Warning "system projection ambiguity";

      let psubst = List.map Stdlib.fst l in
      let projs = List.map Stdlib.snd psubst in
      Some projs, psubst


(*------------------------------------------------------------------*)
(** {2 Misc} *)

(** Exported, see `.mli`. *)
let single_systems_of_context (sc : context) : Single.Set.t option =
  if not (is_fset sc.set) then None else
    let set = to_fset sc.set in
    let pair_fsets =
      match sc.pair with
      | None -> []
      | Some pair ->
        [Stdlib.snd (fst pair); Stdlib.snd (snd pair)]
    in
    let set_fsets = List.map Stdlib.snd (to_list set) in
    some @@
    Single.Set.of_list (pair_fsets @ set_fsets)

(** Exported, see `.mli`. *)
let single_systems_of_se (se : t) : Single.Set.t option =
  if not (is_fset se) then None else
    let set = to_fset se in
    let set_fsets = List.map Stdlib.snd (to_list set) in
    some @@
    Single.Set.of_list set_fsets
