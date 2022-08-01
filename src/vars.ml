open Utils

type var = {
  id : Ident.t;
  ty : Type.ty;
}

type vars = var list

(*------------------------------------------------------------------*)
let is_pat v = String.sub v.id.name 0 1 = "_"

(*------------------------------------------------------------------*)
let name v = v.id.name
let hash v = v.id.tag
let ty   v = v.ty
               
(*------------------------------------------------------------------*)
let norm_ty (env : Type.Infer.env) (v : var) : var =
  { v with ty = Type.Infer.norm env v.ty }

let tsubst s v = { v with ty = Type.tsubst s v.ty }

(*------------------------------------------------------------------*)
let pp ppf v = 
  Fmt.pf ppf "%s%d" (name v) (hash v)

let pp_list ppf l =
  Fmt.pf ppf "@[<hov>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",") pp) l

let pp_typed_list ppf (vars : var list) =
  let rec aux cur_vars cur_type = function
    | v::vs when v.ty = cur_type ->
        aux (v :: cur_vars) cur_type vs
    | vs ->
        if cur_vars <> [] then begin
          Fmt.list
            ~sep:(fun fmt () -> Fmt.pf fmt ",")
            pp ppf (List.rev cur_vars) ;
          Fmt.pf ppf ":%a" Type.pp cur_type ;
          if vs <> [] then Fmt.pf ppf ",@,"
        end ;
        match vs with
          | [] -> ()
          | v :: vs -> aux [v] v.ty vs
  in
  aux [] Type.Message vars


(*------------------------------------------------------------------*)
(** {2 Miscellaneous} *)

let equal (v : var) (v' : var) : bool = v = v'

(** Time-consistent: if [v] was created before [v'], then [compare v v' ≤ 0]. *)
let compare x y =
  if equal x y then 0
  else if x.id.tag <= y.id.tag then -1 else 1

let check_type_vars
    (vars : vars)
    (allowed_types : Type.ty list)
    (error : unit -> unit)
  = 
  List.iter (fun v ->
      if not (List.mem (ty v) allowed_types) then error ()
    ) vars

(*------------------------------------------------------------------*)
(** {2 Set and Maps} *)

let _compare (a : var) (b : var) = Stdlib.compare (a.id.tag) (b.id.tag) 

module Sv = struct
  include Set.Make(struct
      type t = var
      let compare = _compare
    end)

  let hash (set : t) : int =
    fold (fun v h -> hcombine (hash v) h) set 0

  let add_list sv vars =
    List.fold_left (fun sv v -> add v sv) sv vars

  let of_list1 vars = add_list empty vars
end

module Mv = struct
  include Map.Make(struct
      type t = var
      let compare = _compare
    end)
end

(*------------------------------------------------------------------*)
(** {2 Environments} *)

module M = Utils.Ms

type env = var list M.t

let hash_env (e : env) : int =
  M.fold (fun s _ h -> hcombine (Hashtbl.hash s) h) e 0

let to_list (env : env) : var list =
  let _,r2 = M.bindings env |> List.split in
  List.flatten r2

let to_set (env : env) : Sv.t = Sv.of_list (to_list env)

let pp_env ppf e =
  pp_typed_list ppf (to_list e)

let empty_env : env = M.empty

let mem (e : env) var : bool = M.mem (name var) e

let mem_s (e : env) (s : string) : bool = M.mem s e

let find (e : env) (name : string) : var list = M.find name e 

let add_var v (e : env) : env =
  let n = name v in
  let l = M.find_dflt [] n e in
  M.add n (v :: l) e

let add_vars vs (e : env) : env =
  List.fold_left (fun e v -> 
      add_var v e
    ) e vs

let of_list vs : env = add_vars vs empty_env

let of_set s : env = 
  Sv.fold (fun v e -> 
      add_var v e
    ) s empty_env 

let rm_var v (e : env) : env = M.remove (name v) e

let rm_vars vs (e : env) : env = List.fold_left (fun e v -> rm_var v e) e vs

(*------------------------------------------------------------------*)
(** {2 Create new and pattern variables} *)
    
let make_fresh ty name = 
  { id = Ident.create name;
    ty; }

let refresh v =
  { id = Ident.create v.id.name;
    ty = v.ty; }

(*------------------------------------------------------------------*)
(** {2 Create variables} *)

let make ?(allow_pat=false) mode (e : env) ty name =
  assert (allow_pat || name <> "_");
  let e =
    match mode with
    | `Approx -> e
    | `Shadow -> M.filter (fun n _ -> n <> name) e
  in
  let v = make_fresh ty name in
  add_var v e, v

(*------------------------------------------------------------------*)
let make_exact (e : env) ty name =
  if M.mem name e then None
  else
    let v = make_fresh ty name in
    Some (add_var v e, v)

(*------------------------------------------------------------------*)
let make_approx (e : env) v =
  let v' = refresh v in
  add_var v' e, v'

let make_approx_r (e : env ref) v =
  let v' = refresh v in
  e := add_var v' !e;
  v'

