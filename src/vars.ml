open Utils

(* Variables contains two name value, a s_prefix and a i_suffix. The name
   of the variable is then the concatenation of both. This allows, given a set
   of previously defined variables with the same s_prefix, to create the
   simplest possible fresh variable, by incrementing the i_suffix. *)

type 'a var = {
  s_prefix : string;
  i_suffix : int;
  var_type : 'a Type.t
}

type index     = Type.index     var
type message   = Type.message   var
type boolean   = Type.boolean   var
type timestamp = Type.timestamp var

type evar = EVar : 'a var -> evar

(*------------------------------------------------------------------*)
let name v =
  if v.i_suffix <> -1
  then Fmt.strf "%s%i" v.s_prefix v.i_suffix
  else Fmt.strf "%s"   v.s_prefix

let ty v = v.var_type
             
let kind v = Type.kind (v.var_type)

(*------------------------------------------------------------------*)
let pp ppf v =
  Fmt.pf ppf "%s" (name v)

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
(** {2 Environments} *)

module M = Utils.Ms

exception Undefined_Variable

type env = evar M.t

let to_list (e1:env) =
  let _,r2 = M.bindings e1 |> List.split in
  r2

let pp_env ppf e =
  pp_typed_list ppf (to_list e)

let empty_env : env = M.empty

let mem (e : env) name : bool = M.mem name e

let of_list l =
  let rec aux e (l : evar list) =
    match l with
    | [] -> e
    | EVar v :: q ->
      let e = M.add (name v) (EVar v) e in
      aux e q
  in
  aux empty_env l

let rm_var e v = M.remove (name v) e

let rm_evar e (EVar v) = rm_var e v

let prefix_count_regexp = Pcre.regexp "_*([^0-9]*)([0-9]*)"

(*------------------------------------------------------------------*)
(** {2 Create variables} *)

let new_counter = ref 0
    
let make_new_from v =
  let s_prefix = "_" ^ v.s_prefix in
  incr new_counter ;
  { s_prefix ;
    i_suffix = !new_counter ;
    var_type = v.var_type; }

let is_new v = String.sub (name v) 0 1 = "_"

let omax a b = match a,b with
  | None, c | c, None -> c
  | Some a, Some b -> Some (max a b)

let osucc = function
  | None -> Some 0
  | Some i -> Some (i+1)
                        
let max_suffix (e : env) prefix =
  M.fold (fun _ (EVar v') m ->      
      if prefix = v'.s_prefix then
        match m with
        | None -> Some (v'.i_suffix)
        | Some m -> Some (max m v'.i_suffix)
      else m
    ) e None 

let max_suffix_v (e : env) v = max_suffix e v.s_prefix
    
let make_fresh (e1:env) typ s_prefix =
  let s_prefix,i_suffix =
    let substrings = Pcre.exec ~rex:prefix_count_regexp s_prefix in
    let prefix = Pcre.get_substring substrings 1 in
    let i0 = Pcre.get_substring substrings 2 in
    let i0 = if i0 = "" then -1 else int_of_string i0 in
    prefix, i0
  in
  let i_suffix = match max_suffix e1 s_prefix with
    | None -> i_suffix
    | Some m -> max i_suffix (m + 1)
  in

  let v = { s_prefix = s_prefix;
            i_suffix = i_suffix;
            var_type = typ;
          }
  in
  M.add (name v) (EVar v) e1, v 

let make_fresh_and_update (e:env ref) var_type s_prefix =
  let new_env,new_var = make_fresh (!e) var_type s_prefix in
  e := new_env;
  new_var

let make_fresh_from env v =
  make_fresh env v.var_type v.s_prefix

let make_fresh_from_and_update env v =
  make_fresh_and_update env v.var_type v.s_prefix


(*------------------------------------------------------------------*)
(** {2 Set and Maps} *)

module Sv = struct
  include Set.Make(struct
      type t = evar
      let compare (EVar a) (EVar b) = compare (name a) (name b)
    end)
  let add_list sv vars =
    List.fold_left (fun sv v -> add (EVar v) sv) sv vars
end

module Mv = struct
  include Map.Make(struct
      type t = evar
      let compare (EVar a) (EVar b) = compare (name a) (name b)
    end)
end

(*------------------------------------------------------------------*)
(** {2 Miscellaneous} *)

exception CastError

let cast : type a b. a var -> b Type.ty -> b var = 
  fun x s -> match Type.equal_w (ty x) s with
    | Some Type.Type_eq -> x
    | None -> raise CastError

let ecast : type a. evar -> a Type.ty -> a var = 
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
(** {2 Tests} *)

let () =
  Checks.add_suite "Vars" [
    "Prefix extension", `Quick, begin fun () ->
      (* It should never be the case that v.s_prefix is
       * a strict prefix of v'.s_prefix. Otherwise we can
       * have different variables with the same name. *)
      let env = empty_env in
      let env,i = make_fresh env Type.Index "i" in
      let env,i1 = make_fresh env Type.Index "i" in
      let env,i2 = make_fresh env Type.Index "i1" in
      
      Alcotest.(check string)
        "proper name for i"
        "i" (name i);
      Alcotest.(check string)
        "proper name for i0"
        "i0" (name i1);
      Alcotest.(check string)
        "proper name for i1"
        "i1" (name i2);
      Alcotest.(check string)
        "same prefixes"
        i1.s_prefix i.s_prefix ;
      Alcotest.(check string)
        "same prefixes"
        i1.s_prefix i2.s_prefix
    end ;
    "Prefix extension bis", `Quick, begin fun () ->
      (* For backward compatibility, and to avoid refreshing
       * user-provided variable names, we bump the suffix when
       * the user provides a variable name that contains a
       * numerical suffix. *)
      let env = empty_env in
      let env,i1 = make_fresh env Type.Index "i1" in
      let _,i2 = make_fresh env Type.Index "i" in
      let _,i2' = make_fresh env Type.Index "i1" in
      let _,i2'' = make_fresh env Type.Index "i2" in
      Alcotest.(check string)
        "Biproper name for i1 (bis)"
        (name i1) "i1" ;
      Alcotest.(check string)
        "proper name for i2 (bis)"
        (name i2) "i2" ;
      Alcotest.(check string)
        "proper name for i2' (bis)"
        (name i2') "i2" ;
      Alcotest.(check string)
        "proper name for i2'' (bis)"
        (name i2'') "i2"
    end ]
