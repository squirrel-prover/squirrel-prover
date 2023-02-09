open Utils

type var = {
  id : Ident.t;
  ty : Type.ty;
}

type vars = var list


(*------------------------------------------------------------------*)
(** {2 Variable scope} *)

(** A variable can have a local or global scope. *)
type scope = Local | Global

(*------------------------------------------------------------------*)
(** {2 Variable information} *)

module Tag = struct

  (** Variable information restricting its possible instanciations. *)
  type t = {
    const : bool;
    (** var represents a constant computation *)

    system_indep : bool;
    (** var must be instantiated by a term representiang a
        system-independent computation *)
  }

  (*------------------------------------------------------------------*)
  let pp fmt { const; system_indep; } =
    let l =
      (if const then ["const"] else []) @
      (if system_indep then ["glob"] else [])
    in
    if l = [] then ()
    else
      Fmt.pf fmt "@[<h>[%a]@]" (Fmt.list ~sep:Fmt.comma Fmt.string) l

  (*------------------------------------------------------------------*)
  let make ?(const = false) (sc : scope) : t =
    match sc with
    | Local  -> { const; system_indep = false; }
    | Global -> { const; system_indep = true; }

  (*------------------------------------------------------------------*)
  (** default local tag *)               
  let ltag = make Local

  (** default global tag *)
  let gtag = make Global

  (*------------------------------------------------------------------*)
  let local_vars ?(const = false) (vs : vars) : (var * t) list =
    List.map (fun v -> v, make ~const Local) vs

  let global_vars ?(const = false) (vs : vars) : (var * t) list =
    List.map (fun v -> v, make ~const Global) vs
end

type tagged_var = var * Tag.t

type tagged_vars = (var * Tag.t) list

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
    (Fmt.list ~sep:(Fmt.any ",") (_pp ~dbg)) l

let _pp_typed_list_w_info pp_info ~dbg ppf (vars : (var * 'a) list) =
  let rec aux cur_vars cur_type cur_info = function
    | (v, info)::vs when v.ty = cur_type && info = cur_info ->
      aux (v :: cur_vars) cur_type cur_info vs 
    | vs ->
      if cur_vars <> [] then begin
        Fmt.list
          ~sep:(Fmt.any ",")
          (_pp ~dbg) ppf (List.rev cur_vars) ;
        Fmt.pf ppf ":%a%a" Type.pp cur_type pp_info cur_info;
        if vs <> [] then Fmt.pf ppf ",@,"
      end ;
      match vs with
      | [] -> ()
      | (v, info) :: vs -> aux [v] v.ty info vs
  in
  match vars with
  | [] -> ()
  | (v, info) :: vars -> aux [v] v.ty info vars

let _pp_typed_list ~dbg ppf (vars : 'a list) : unit =
  _pp_typed_list_w_info (fun _ _ -> ()) ~dbg ppf (List.map (fun v -> (v, ())) vars)
  
(*------------------------------------------------------------------*)
(** Exported *)
let pp            = _pp            ~dbg:false
let pp_list       = _pp_list       ~dbg:false
let pp_typed_list = _pp_typed_list ~dbg:false

let _pp_typed_tagged_list = _pp_typed_list_w_info Tag.pp 
let pp_typed_tagged_list  = _pp_typed_list_w_info Tag.pp ~dbg:false
    
(*------------------------------------------------------------------*)
(** {2 Debug printing} *)

(** Exported *)
let pp_dbg            = _pp            ~dbg:true
let pp_list_dbg       = _pp_list       ~dbg:true
let pp_typed_list_dbg = _pp_typed_list ~dbg:true

let pp_typed_tagged_list_dbg = _pp_typed_list_w_info Tag.pp ~dbg:true
    
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

type 'a genv = (var * 'a) list Ms.t

(*------------------------------------------------------------------*)
type simpl_env = unit genv

type env = Tag.t genv

(*------------------------------------------------------------------*)
let to_list (env : 'a genv) : (var * 'a) list =
  List.concat_map (fun (_, l) -> l) (Ms.bindings env) 

let to_vars_list (env : 'a genv) : var list =
  List.map fst (to_list env)

let to_vars_set (env : 'a genv) : Sv.t = Sv.of_list (to_vars_list env)

let to_map (env : 'a genv) : 'a Mv.t =
  List.fold_left (fun m (x,a) -> Mv.add x a m) Mv.empty (to_list env)

(*------------------------------------------------------------------*)
let sanity_check (e : 'a genv) = 
  assert (Ms.for_all (fun _ l -> List.length l = 1) e)

(*------------------------------------------------------------------*)
let _pp_genv ~dbg pp_info ppf (e : 'a genv) =
  _pp_typed_list_w_info pp_info ~dbg ppf (to_list e)

let pp_genv     pp_info = _pp_genv ~dbg:false pp_info
let pp_genv_dbg pp_info = _pp_genv ~dbg:true  pp_info

(*------------------------------------------------------------------*)
let _pp_env ~dbg = _pp_genv ~dbg Tag.pp
let  pp_env      =  pp_genv      Tag.pp
let  pp_env_dbg  =  pp_genv_dbg  Tag.pp

(*------------------------------------------------------------------*)
let empty_env : 'a genv = Ms.empty

let mem (e : 'a genv) var : bool = 
  let l = Ms.find_dflt [] (name var) e in
  List.exists (fun (var',_) -> equal var var') l

let mem_s (e : 'a genv) (s : string) : bool = Ms.mem s e

let find (e : 'a genv) (name : string) : (var * 'a) list = Ms.find name e

(*------------------------------------------------------------------*)
let get_info (v : var) (env : 'a genv) : 'a =
  let _, i = List.find (fun (v', _) -> equal v v') (find env (name v)) in
  i

(*------------------------------------------------------------------*)
let add_var v (info : 'a) (e : 'a genv): 'a genv =
  let n = name v in
  let l = Ms.find_dflt [] n e in
  Ms.add n ((v,info) :: l) e

let add_vars vs (e : 'a genv) : 'a genv =
  List.fold_left (fun e (v,info) -> 
      add_var v info e
    ) e vs

let add_var_simpl v (e : simpl_env) : simpl_env = add_var v () e

let add_vars_simpl vs (e : simpl_env) : simpl_env =
  add_vars (List.map (fun x -> (x, ())) vs) e
    
(*------------------------------------------------------------------*)
let of_list vs : 'a genv = add_vars vs empty_env

let of_set s : simpl_env = 
  Sv.fold (fun v e -> 
      add_var_simpl v e
    ) s empty_env 

let of_map (m : 'a Mv.t) : 'a genv = 
  Mv.fold (fun v i e -> 
      add_var v i e
    ) m empty_env 

(*------------------------------------------------------------------*)
let to_simpl_env (env : 'a genv) : simpl_env =
  Ms.map (fun l ->
      List.map (fun (v, _) -> v, ()) l
    ) env

(*------------------------------------------------------------------*)
let rm_var v (e : 'a genv) : 'a genv = 
  assert (mem e v);
  let v_name = name v in
  let l = Ms.find_dflt [] v_name e in
  let l = List.filter (fun (v', _) -> not (Ident.equal v.id v'.id)) l in
  if l <> [] then Ms.add v_name l e else Ms.remove v_name e

let rm_vars vs (e : 'a genv) : 'a genv =
  List.fold_left (fun e v -> rm_var v e) e vs

(*------------------------------------------------------------------*)
let map_tag (f : var -> Tag.t -> Tag.t) (e : env) : env =
  Ms.map (fun l -> List.map (fun (v,t) -> v, f v t) l) e

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
let make_suffix (e : 'a genv) (prefix : string) : int option =
  assert (prefix <> "_");

  Ms.fold (fun _ vars max ->
      List.fold_left (fun max (var, _info) ->
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

let make_name ~allow_pat (env : 'a genv) (name : string) : string =
  let s_prefix, s_suffix = split_var_name name in
  assert (check_prefix ~allow_pat s_prefix);

  let i_suffix = int_of_string s_suffix in

  if not (Ms.mem name env) then name (* [name] not in use *)
  else (* [name] in use, find another name close to [name] *)
    let s_suffix =
      match make_suffix env s_prefix with
      | None -> assert false      (* impossible *)
      | Some m -> max i_suffix (m + 1)
    in
    s_prefix ^ int_suffix_to_string s_suffix

(*------------------------------------------------------------------*)
let make
    ?(allow_pat=false) mode (e : 'a genv) (ty : Type.ty) (name : string) (info : 'a)
  : 'a genv * var
  =
  assert (allow_pat || name <> "_");

  (* if mode is [`Shadow], shadow existing variables in [e] *)
  let e =
    match mode with
    | `Approx -> e
    | `Shadow ->
      assert (name <> "_");
      Ms.filter (fun n _ -> n <> name) e
  in
  let fresh_name =
    match mode with
    | `Shadow -> name (* if `Shadow, we reuse the name *)
    | `Approx ->
      make_name ~allow_pat e name
  in
  assert (not (Ms.mem fresh_name e));
  
  let v = { id = Ident.create fresh_name; ty; } in
  add_var v info e, v

let make_local
    ?allow_pat mode (e : env) (ty : Type.ty) (name : string) 
  : env * var
  =
  make ?allow_pat mode e ty name (Tag.make Local)

let make_global
    ?allow_pat mode (e : env) (ty : Type.ty) (name : string) 
  : env * var
  =
  make ?allow_pat mode e ty name (Tag.make Global)

(*------------------------------------------------------------------*)
let make_exact (e : 'a genv) ty name info =
  if Ms.mem name e then None
  else
    let v = make_fresh ty name in
    Some (add_var v info e, v)

(*------------------------------------------------------------------*)
let make_approx (e : 'a genv) v (info : 'a) =
  make `Approx e v.ty v.id.name info

let make_approx_r (e : 'a genv ref) v (info : 'a) =
  let e', v' = make_approx !e v info in
  e := e';
  v'
                                          
(*------------------------------------------------------------------*)
(** {2 Tests} *)

let () =
  Checks.add_suite "Vars" [
    "Prefix extension", `Quick, begin fun () ->
      let  env = empty_env in
      let  env,i  = make `Approx env Type.Index "i"  () in
      let  env,i0 = make `Approx env Type.Index "i"  () in
      let _env,i1 = make `Approx env Type.Index "i1" () in
      
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
