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
(** {2 Pretty-printing} *)

let _pp ~dbg ppf v = 
  if dbg then
    Fmt.pf ppf "%s/%d" (name v) (hash v)
  else
    Fmt.pf ppf "%s" (name v)

let _pp_list ~dbg ppf l =
  Fmt.pf ppf "@[<hov>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",") (_pp ~dbg)) l

let _pp_typed_list ~dbg ppf (vars : var list) =
  let rec aux cur_vars cur_type = function
    | v::vs when v.ty = cur_type ->
        aux (v :: cur_vars) cur_type vs
    | vs ->
        if cur_vars <> [] then begin
          Fmt.list
            ~sep:(fun fmt () -> Fmt.pf fmt ",")
            (_pp ~dbg) ppf (List.rev cur_vars) ;
          Fmt.pf ppf ":%a" Type.pp cur_type ;
          if vs <> [] then Fmt.pf ppf ",@,"
        end ;
        match vs with
          | [] -> ()
          | v :: vs -> aux [v] v.ty vs
  in
  aux [] Type.Message vars

(*------------------------------------------------------------------*)
(** Exported *)
let pp            = _pp            ~dbg:false
let pp_list       = _pp_list       ~dbg:false
let pp_typed_list = _pp_typed_list ~dbg:false

(*------------------------------------------------------------------*)
(** {2 Debug printing} *)

(** Exported *)
let pp_dbg            = _pp            ~dbg:true
let pp_list_dbg       = _pp_list       ~dbg:true
let pp_typed_list_dbg = _pp_typed_list ~dbg:true


(*------------------------------------------------------------------*)
(** {2 Miscellaneous} *)

let equal (v : var) (v' : var) : bool = Ident.equal v.id v'.id

(** Time-consistent: if [v] was created before [v'], then [compare v v' ≤ 0]. *)
let compare x y =
  if Ident.equal x.id y.id then 0
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
(** {2 Create variables} *)

(*------------------------------------------------------------------*)
let make_fresh ty name = 
  { id = Ident.create name;
    ty; }

let refresh v =
  { id = Ident.create v.id.name;
    ty = v.ty; }

(*------------------------------------------------------------------*)
let prefix_count_regexp = Pcre.regexp "#*(_*.*[^0-9])([0-9]*)$"

(* Split a string [name] into a prefix [s] and an suffix [i] which is 
   a string representing a base 10 integer.
   We have that [name = s ^ i] if [i >= 0], and [name = s] if [i = -1]. *)
let split_var_name (name : string) : string * string =
  let substrings = Pcre.exec ~rex:prefix_count_regexp name in
  let s = Pcre.get_substring substrings 1 in

  let i = Pcre.get_substring substrings 2 in

  let i = if i = "" then "-1" else i in
  s, i

let int_suffix_to_string (i : int) : string =
  if i = -1 then "" else string_of_int i

(* Compute the suffix to add to [prefix] such that [prefix ^ suffix] 
   is fresh in [e]. *)
let make_suffix (e : env) (prefix : string) : int option =
  assert (prefix <> "_");

  M.fold (fun _ vars max ->
      List.fold_left (fun max var ->
          let s_prefix, s_suffix = split_var_name var.id.name in
          if prefix = s_prefix then
            let i_suffix = int_of_string s_suffix in
            match max with
            | None -> Some i_suffix
            | Some max -> Some (Stdlib.max max i_suffix)
          else max
        ) max vars
    ) e None

let check_prefix ~allow_pat s =
  (s = "_" || String.sub s 0 1 <> "_") &&
  (if not allow_pat then String.sub s 0 1 <> "_" else true)

let make_name ~allow_pat (env : env) (name : string) : string =
  let s_prefix, s_suffix = split_var_name name in
  assert (check_prefix ~allow_pat s_prefix);

  let i_suffix = int_of_string s_suffix in

  if not (M.mem name env) then name (* [name] not in use *)
  else (* [name] in use, find another name close to [name] *)
    let s_suffix =
      match make_suffix env s_prefix with
      | None -> assert false      (* impossible *)
      | Some m -> max i_suffix (m + 1)
    in
    s_prefix ^ int_suffix_to_string s_suffix

(*------------------------------------------------------------------*)
let make ?(allow_pat=false) mode (e : env) ty name =
  assert (allow_pat || name <> "_");

  (* if mode is [`Shadow], shadow existing variables in [e] *)
  let e =
    match mode with
    | `Approx -> e
    | `Shadow ->
      assert (name <> "_");
      M.filter (fun n _ -> n <> name) e
  in
  let fresh_name =
    match mode with
    | `Shadow -> name (* if `Shadow, we reuse the name *)
    | `Approx ->
      make_name ~allow_pat e name
  in
  assert (not (M.mem fresh_name e));
  
  let v = { id = Ident.create fresh_name; ty; } in
  add_var v e, v

(*------------------------------------------------------------------*)
let make_exact (e : env) ty name =
  if M.mem name e then None
  else
    let v = make_fresh ty name in
    Some (add_var v e, v)

(*------------------------------------------------------------------*)
let make_approx (e : env) v =
  make `Approx e v.ty v.id.name 

let make_approx_r (e : env ref) v =
  let e', v' = make_approx !e v in
  e := e';
  v'
                                          
(*------------------------------------------------------------------*)
(** {2 Tests} *)

let () =
  Checks.add_suite "Vars" [
    "Prefix extension", `Quick, begin fun () ->
      let env = empty_env in
      let env,i  = make `Approx env Type.Index "i"  in
      let env,i0 = make `Approx env Type.Index "i"  in
      let env,i1 = make `Approx env Type.Index "i1" in
      
      Alcotest.(check string)
        "proper name for i"
        "i" (name i);
      Alcotest.(check string)
        "proper name for i0"
        "i0" (name i0);
      Alcotest.(check string)
        "proper name for i1"
        "i1" (name i1);
    end ;]
