open Utils

type 'a var = {
  name     : string;
  s_prefix : string;
  i_suffix : int; 
  is_new   : bool;
  var_type : 'a Type.t
}

type 'a vars = 'a var list

(* [i_suffix] is stored to avoid recomputing it.
   we use it as a unique counter for new and pat variables. *)

type index     = Type.index     var
type message   = Type.message   var
type boolean   = Type.message   var
type timestamp = Type.timestamp var

type evar = EVar : 'a var -> evar

type evars = evar list

let evar v = EVar v

(*------------------------------------------------------------------*)
let is_new v = v.is_new
let is_pat v = String.sub v.name 0 1 = "_"

(*------------------------------------------------------------------*)
let name v = (if v.is_new then "#" else "") ^ v.name

let hash v  = Hashtbl.hash (name v)
let ehash (EVar v) = hash v

let ty v = v.var_type
let ety (EVar v) = Type.ETy v.var_type

let norm_ty : type a. Type.Infer.env -> a var -> a var =
  fun env v ->
  { v with var_type = Type.Infer.norm env v.var_type }

let enorm_ty env (EVar v) = EVar (norm_ty env v)
             
let kind v = Type.kind (v.var_type)

let tsubst s v = { v with var_type = Type.tsubst s v.var_type }
let tsubst_e s (EVar v) = EVar (tsubst s v)

(*------------------------------------------------------------------*)
let pp ppf v = 
  Fmt.pf ppf "%s%s" (name v) (if v.is_new then string_of_int v.i_suffix else "")

let pp_e ppf (EVar v) = pp ppf v

let pp_list ppf l =
  Fmt.pf ppf "@[<hov>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",") pp) l

let pp_typed_list ppf (vars:evar list) =
  let rec aux cur_vars cur_type = function
    | EVar v::vs when Type.ETy v.var_type = cur_type ->
        aux (EVar v::cur_vars) cur_type vs
    | vs ->
        if cur_vars <> [] then begin
          Fmt.list
            ~sep:(fun fmt () -> Fmt.pf fmt ",")
            pp_e ppf (List.rev cur_vars) ;
          Fmt.pf ppf ":%a" Type.pp_e cur_type ;
          if vs <> [] then Fmt.pf ppf ",@,"
        end ;
        match vs with
          | [] -> ()
          | EVar v::vs -> aux [EVar v] (Type.ETy v.var_type) vs
  in
  aux [] Type.(ETy Message) vars


(*------------------------------------------------------------------*)
(** {2 Miscellaneous} *)

exception CastError

let cast : type a b. a var -> b Type.kind -> b var = 
  fun x s -> match Type.equalk_w (kind x) s with
    | Some Type.Type_eq -> x
    | None -> raise CastError

let ecast : type a. evar -> a Type.kind -> a var = 
  fun (EVar v) s -> cast v s

let equal : type a b. a var -> b var -> bool = fun v v' ->
  match Type.equal_w (ty v) (ty v') with
  | None -> false
  | Some Type.Type_eq -> v = v'

(** Time-consistent: if [v] was created before [v'], then [compare v v' ≤ 0]. *)
let compare x y =
  if equal x y then 0
  else if x.i_suffix <= y.i_suffix then -1 else 1


(*------------------------------------------------------------------*)
(** {2 Set and Maps} *)

module Sv = struct
  include Set.Make(struct
      type t = evar
      let compare (EVar a) (EVar b) = 
        Stdlib.compare 
          (a.name, a.s_prefix, a.is_new, a.i_suffix) 
          (b.name, b.s_prefix, b.is_new, b.i_suffix) 
    end)

  let hash (set : t) : int =
    fold (fun v h -> hcombine (ehash v) h) set 0

  let add_list sv vars =
    List.fold_left (fun sv v -> add (EVar v) sv) sv vars

  let of_list1 vars = add_list empty vars
end

module Mv = struct
  include Map.Make(struct
      type t = evar
      let compare (EVar a) (EVar b) = 
        Stdlib.compare 
          (a.name, a.s_prefix, a.is_new, a.i_suffix) 
          (b.name, b.s_prefix, b.is_new, b.i_suffix) 
    end)
end

(*------------------------------------------------------------------*)
(** {2 Environments} *)

module M = Utils.Ms

type env = evar M.t

let hash_env (e : env) : int =
  M.fold (fun s _ h -> hcombine (Hashtbl.hash s) h) e 0

let to_list (env : env) =
  let _,r2 = M.bindings env |> List.split in
  r2

let to_set (env : env) : Sv.t = Sv.of_list (to_list env)

let pp_env ppf e =
  pp_typed_list ppf (to_list e)

let empty_env : env = M.empty

let mem (e : env) var : bool = M.mem (name var) e

let mem_e (e : env) (EVar var) : bool = M.mem (name var) e

let mem_s (e : env) (s : string) : bool = M.mem s e

let find : type a. env -> string -> a Type.kind -> a var = 
  fun e name k -> 
  (* let EVar v = 
   *   let found = ref None in
   *   let exception Found in
   *   try
   *     let () = 
   *       M.iter (fun id v -> 
   *           if id = name then 
   *             let () = found := Some v in
   *             raise Found) e 
   *     in
   *     raise Not_found
   * 
   *   with Found -> oget !found
   * in *)
  let EVar v = M.find name e in
  cast v k

let of_list l : env =
  List.fold_left (fun e (EVar v) -> 
      M.add (name v) (EVar v) e
    ) empty_env l

let of_set s : env = 
  Sv.fold (fun (EVar v) e -> 
      M.add (name v) (EVar v) e
    ) s empty_env 

let rm_var e v = M.remove (name v) e

let rm_vars e vs = List.fold_left rm_var e vs

let rm_evar e (EVar v) = rm_var e v

let rm_evars e vs = List.fold_left rm_evar e vs

let prefix_count_regexp = Pcre.regexp "#*(_*.*[^0-9])([0-9]*)$"

(*------------------------------------------------------------------*)
(** {2 Create new and pattern variables} *)
    
let cpt_new = ref 0

let make_new ty name = 
  incr cpt_new;
  { name     = name;
    s_prefix = name;
    i_suffix = !cpt_new;
    is_new   = true;
    var_type = ty; }

let make_new_from v =
  incr cpt_new;
  { v with name     = v.s_prefix;
           is_new   = true; 
           i_suffix = !cpt_new; }

(*------------------------------------------------------------------*)
let cpt_pat = ref 0

let make_pat typ = 
  incr cpt_pat;
  { name     = "_" ^ (string_of_int !cpt_pat);
    s_prefix = "_";
    is_new   = false;
    i_suffix = !cpt_pat;
    var_type = typ; }

(*------------------------------------------------------------------*)
(** {2 Create variables} *)
                        
let max_suffix (e : env) prefix =
  assert (prefix <> "_");
  M.fold (fun _ (EVar v') m ->      
      if prefix = v'.s_prefix then
        match m with
        | None -> Some (v'.i_suffix)
        | Some m -> Some (max m v'.i_suffix)
      else m
    ) e None 
    
let check_prefix ~allow_pat s =
  (s = "_" || String.sub s 0 1 <> "_") &&
  (if not allow_pat then String.sub s 0 1 <> "_" else true)


let _make opt env s_prefix s_suffix = 
  let i = if s_suffix = "" then -1 else int_of_string s_suffix in
  
  match opt, max_suffix env s_prefix with
    | `Shadow, _ -> i (* if `Shadow, we can reuse the suffix *)
    | _, None -> i
    | _, Some m -> max i (m + 1)
  

let make ?(allow_pat=false) opt (env : env) typ s_name =
  let substrings = Pcre.exec ~rex:prefix_count_regexp s_name in
  let s_prefix = Pcre.get_substring substrings 1 in
  let s_suffix = Pcre.get_substring substrings 2 in
  assert (check_prefix ~allow_pat (s_prefix));

  let v = 
    if s_prefix = "_" then make_pat typ 
    else
      let i_suffix = _make opt env s_prefix s_suffix in
      let s_suffix = if i_suffix = -1 then "" else string_of_int i_suffix in      
      let name = s_prefix ^ s_suffix in

      if opt = `Shadow then assert (name = s_name);

      { name; s_prefix; is_new = false; i_suffix; var_type = typ; }
  in
  assert (name v = v.name);

  let env = M.add v.name (EVar v) env in
  env, v 

let make_r ?allow_pat opt (e:env ref) var_type s_prefix =
  let new_env,new_var = make ?allow_pat opt (!e) var_type s_prefix in
  e := new_env;
  new_var

let make_exact e typ s = 
  let e, v = make `Approx e typ s in
  if name v <> s then None else Some (e,v)

let make_exact_r e typ s = 
  let v = make_r `Approx e typ s in
  if name v <> s then None else Some v

let fresh env v = make `Approx env v.var_type (name v)

let fresh_r env v = make_r `Approx env v.var_type (name v)

                                          
(*------------------------------------------------------------------*)
(** {2 Tests} *)

let () =
  Checks.add_suite "Vars" [
    "Prefix extension", `Quick, begin fun () ->
      (* It should never be the case that v.s_prefix is
       * a strict prefix of v'.s_prefix. Otherwise we can
       * have different variables with the same name. *)
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
      Alcotest.(check int)
        "integer suffix"
        i.i_suffix (-1);
      Alcotest.(check int)
        "integer suffix"
        i0.i_suffix 0;
      Alcotest.(check int)
        "integer suffix"
        i1.i_suffix 1;
    end ;]
