type sort =  Message | Boolean | Index | Timestamp

let pp_type ppf = function
  | Message -> Fmt.pf ppf "message"
  | Index -> Fmt.pf ppf "index"
  | Timestamp -> Fmt.pf ppf "timestamp"
  | Boolean -> Fmt.pf ppf "bool"

(* Variables contains two name value, a name_prefix and a name_suffix. The name
   of the variable is then the concatenation of both. This allows, given a set
   of previously defined variables with the same name_prefix, to create the
   simplest possible fresh variable, by incrementing the name_suffix. *)
type var = {name_prefix : string; name_suffix : int; var_type : sort }

let name v =
  if v.name_suffix <> 0 then
    Fmt.strf "%s%i" v.name_prefix v.name_suffix
  else
    Fmt.strf "%s" v.name_prefix

let var_type v = v.var_type

let pp ppf (v:var) =
  Fmt.pf ppf "%s" (name v)

let pp_typed ppf (v:var) =
  Fmt.pf ppf "%a:%a" pp v pp_type v.var_type

let pp_list ppf l =
  Fmt.pf ppf "@[<hov>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",") pp) l

let pp_typed_list ppf vars =
  let rec aux cur_vars cur_type = function
    | v::vs when v.var_type = cur_type ->
        aux (v::cur_vars) cur_type vs
    | vs ->
        if cur_vars <> [] then begin
          Fmt.list
            ~sep:(fun fmt () -> Fmt.pf fmt ",")
            pp ppf (List.rev cur_vars) ;
          Fmt.pf ppf ":%a" pp_type cur_type ;
          if vs <> [] then Fmt.pf ppf ",@,"
        end ;
        match vs with
          | [] -> ()
          | v::vs -> aux [v] v.var_type vs
  in
  aux [] Message vars

module M = Map.Make(String)

exception Undefined_Variable

exception Variable_Already_Defined

(* An environment is made of two maps. One maps variables names
   (accordingly to [var_name]) to variables, and the second maps
   name prefixes to the current biggest name_suffix for this
   name_prefix. *)
type env = (var M.t * int M.t)

let to_list (e1,e2) =
  let r1,r2 = M.bindings e1 |> List.split in
  r2

let pp_env ppf e =
  pp_list ppf (to_list e)

let pp_typed_env ppf e =
  pp_typed_list ppf (to_list e)

let empty_env : env = (M.empty,M.empty)

let mem (e1,e2) name =
  M.mem name e1

let get_var (e1,e2) name =
  try
    M.find name e1
  with Not_found -> raise Undefined_Variable

let make_fresh (e1,e2) var_type name_prefix =
  let name_suffix =
    try
      (M.find name_prefix e2) + 1
    with Not_found -> 0
  in
  let v = { name_prefix = name_prefix;
            name_suffix = name_suffix;
            var_type = var_type;
          }
  in
  ( (M.add (name v) v e1, M.add name_prefix name_suffix e2), v  )

let make_fresh_and_update (e:env ref) var_type name_prefix =
  let new_env,new_var = make_fresh (!e) var_type name_prefix in
  e := new_env;
  new_var

let make_fresh_from env (v:var) =
  make_fresh env v.var_type v.name_prefix

let make_fresh_from_and_update env (v:var) =
  make_fresh_and_update env v.var_type v.name_prefix
