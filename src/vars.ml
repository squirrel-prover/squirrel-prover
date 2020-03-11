(* Variables contains two name value, a name_prefix and a name_suffix. The name
   of the variable is then the concatenation of both. This allows, given a set
   of previously defined variables with the same name_prefix, to create the
   simplest possible fresh variable, by incrementing the name_suffix. *)

type 'a var =
  {name_prefix : string;
   name_suffix : int;
   var_type : 'a Sorts.t }

type index = Sorts.index var
type message = Sorts.message var
type boolean = Sorts.boolean var
type timestamp = Sorts.timestamp var

type evar = EVar : 'a var -> evar

let name v =
  if v.name_suffix <> 0 then
    Fmt.strf "%s%i" v.name_prefix v.name_suffix
  else
    Fmt.strf "%s" v.name_prefix

let sort v = v.var_type

let pp ppf v =
  Fmt.pf ppf "%s" (name v)

let pp_e ppf (EVar v) = pp ppf v

let pp_list ppf l =
  Fmt.pf ppf "@[<hov>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",") pp) l

let pp_typed_list ppf (vars:evar list) =
  let rec aux cur_vars cur_type = function
    | EVar v::vs when Sorts.ESort v.var_type = cur_type ->
        aux (EVar v::cur_vars) cur_type vs
    | vs ->
        if cur_vars <> [] then begin
          Fmt.list
            ~sep:(fun fmt () -> Fmt.pf fmt ",")
            pp_e ppf (List.rev cur_vars) ;
          Fmt.pf ppf ":%a" Sorts.pp_e cur_type ;
          if vs <> [] then Fmt.pf ppf ",@,"
        end ;
        match vs with
          | [] -> ()
          | EVar v::vs -> aux [EVar v] (Sorts.ESort v.var_type) vs
  in
  aux [] Sorts.(ESort Message) vars

module M = Map.Make(String)

exception Undefined_Variable

(* An environment is made of two maps. One maps variables names
   (accordingly to [var_name]) to variables, and the second maps
   name prefixes to the current biggest name_suffix for this
   name_prefix. *)
type env = (evar M.t * int M.t)

let to_list ((e1,_):env) =
  let _,r2 = M.bindings e1 |> List.split in
  r2

let pp_env ppf e =
  pp_typed_list ppf (to_list e)

let empty_env : env = (M.empty,M.empty)

let mem (e1,_) name =
  M.mem name e1

let get_var (e1,_) name =
  try
    M.find name e1
  with Not_found -> raise Undefined_Variable

let of_list l =
  let rec aux (e1, e2) (l : evar list) =
    match l with
    | [] -> (e1, e2)
    | (EVar v)::q -> aux (M.add (name v) (EVar v) e1,
                          M.add v.name_prefix v.name_suffix e2) q
  in
  aux empty_env l

let rm_var (e1,e2) v =
   let name_suffix =
    try
      (M.find v.name_prefix e2)
    with Not_found -> 0
   in
   let new_suffix =
     if name_suffix = v.name_suffix then name_suffix -1 else name_suffix
   in
  M.remove (name v) e1, M.add v.name_prefix new_suffix e2

let make_fresh ((e1,e2):env) var_type name_prefix =
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
  ( (M.add (name v) (EVar v) e1, M.add name_prefix name_suffix e2), v  )

let make_fresh_and_update (e:env ref) var_type name_prefix =
  let new_env,new_var = make_fresh (!e) var_type name_prefix in
  e := new_env;
  new_var

let make_fresh_from env v =
  make_fresh env v.var_type v.name_prefix

let make_fresh_from_and_update env v =
  make_fresh_and_update env v.var_type v.name_prefix
