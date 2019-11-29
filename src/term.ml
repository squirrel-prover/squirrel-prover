open Vars

open Action

type timestamp =
  | TVar of var
  | TPred of timestamp
  | TName of action

let rec pp_timestamp ppf = function
  | TVar tv -> Vars.pp ppf tv
  | TPred ts -> Fmt.pf ppf "@[<hov>p(%a)@]" pp_timestamp ts
  | TName a -> Action.pp_action ppf a

let rec action_of_ts = function
  | TName a -> Some a
  | TPred ts -> action_of_ts ts
  | TVar _ -> None

let rec tsvars vs = function
  | TVar tv -> tv :: vs
  | TName a ->  action_indices a @ vs
  | TPred ts -> tsvars vs ts

let ts_vars =
  tsvars []
type mvar = Vars.var

type name = Name of string

(* TODO having [name] abstract makes no sense currently
 * since we can freely create names from strings *)
let string_of_name (Name s) = s
let mk_name x = Name x
let pp_name ppf = function Name s -> (Utils.kw `Yellow) ppf s

type nsymb = name * index list
let pp_nsymb ppf (n,is) =
  if is <> [] then Fmt.pf ppf "%a(%a)" pp_name n Vars.pp_list is
  else Fmt.pf ppf "%a" pp_name n

(* TODO must include builtins such as if-then-else, equality, successor, xor ...
  * Adrien: already added some
  * Some keywords should probably be forbidden, e.g. "input", "output"
*)

type fname = Fname of string

let pp_fname ppf = function Fname s -> (Utils.kw `Bold) ppf s

type fsymb = fname * index list

let pp_fsymb ppf (fn,is) = match is with
  | [] -> Fmt.pf ppf "%a" pp_fname fn
  | _ -> Fmt.pf ppf "%a[%a]" pp_fname fn Vars.pp_list is

let mk_fname f = (Fname f, [])
let mk_fname_idx f l = (Fname f, l)

(** Boolean function symbols *)
let f_false = (Fname "false", [])
let f_true = (Fname "true", [])
let f_and = (Fname "and", [])
let f_or = (Fname "or", [])
let f_not = (Fname "not", [])

(** IfThenElse function symbol *)
let f_ite = (Fname "if", [])

(** Xor function symbol *)
let f_xor = (Fname "xor", [])

(** Zero function symbol. Satisfies 0 + a -> a *)
let f_zero = (Fname "zero", [])

(** Successor function symbol *)
let f_succ = (Fname "succ", [])

(* TODO simplify design to merge name, function and state names ? *)

type sname = Sname of string
let mk_sname x = Sname x

let pp_sname ppf = function Sname s -> (Utils.kw `Red) ppf s

type state = sname * index list

let pp_state ppf (sn,is) =
  if is <> [] then Fmt.pf ppf "%a(%a)" pp_sname sn Vars.pp_list is
  else Fmt.pf ppf "%a" pp_sname sn

(** Type of macros name *)
type mname = string
type msymb = mname * index list

let pp_mname ppf s =
  let open Fmt in
  (styled `Bold (styled `Magenta Utils.ident)) ppf s

let pp_msymb ppf (m,is) =
  Fmt.pf ppf "%a%a"
    pp_mname m
    (Utils.pp_ne_list "(%a)" Vars.pp_list) is

(** Terms *)
type term =
  | Fun of fsymb * term list
  | Name of nsymb
  | MVar of mvar
  | State of state * timestamp
  | Macro of msymb * timestamp

let dummy = Fun ((Fname "_", []), [])

let rec pp_term ppf = function
  | Fun ( (Fname s,ids) , terms) ->
    if s = "pair" then
      Fmt.pf ppf "%a"
        (Utils.pp_ne_list
           "<@[<hov>%a@]>"
           (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,") pp_term)) terms
    else
      let f =  (Fname s,ids) in
      Fmt.pf ppf "%a%a"
        pp_fsymb f
        (Utils.pp_ne_list
           "(@[<hov>%a@])"
           (Fmt.list ~sep:Fmt.comma pp_term)) terms
  | Name n -> pp_nsymb ppf n
  | State (s, ts) -> Fmt.pf ppf "@[%a@%a@]" pp_state s pp_timestamp ts
  | Macro (m, ts) -> Fmt.pf ppf "@[%a@%a@]" pp_msymb m pp_timestamp ts
  | MVar m -> Fmt.pf ppf "%a" Vars.pp m

type t = term


let rec tvars acc = function
  | Fun ((_, is) , lt) -> List.fold_left tvars (is@acc) lt
  | Name (_, is) ->  is@acc
  | State ((_, is), ts) -> tsvars (is@acc) ts
  (* | Input ts *)
  | Macro (_, ts) -> tsvars acc ts
  | MVar _ ->  []

let term_vars t =
  tvars [] t
  |> List.sort_uniq Pervasives.compare

let rec tts acc = function
  | Fun (fs, lt) -> List.fold_left tts acc lt
  | Name n -> acc
  | State (_, ts)
  (* | Input ts *)
  | Macro (_, ts) -> ts :: acc
  | MVar _ -> []

let term_ts t = tts [] t |> List.sort_uniq Pervasives.compare


let macros : (string, int * (action -> index list -> term)) Hashtbl.t =
  Hashtbl.create 97

let initialize_macros () = Hashtbl.clear macros

let built_ins = ["input";"output"]

(** [is_built_in mn] returns true iff [mn] is a built-in.  *)
let is_built_in mn = List.mem mn built_ins

let is_declared mn =
  if Hashtbl.mem macros mn || List.mem mn built_ins then mn
  else raise Not_found

exception Reserved_identifier
exception Multiple_declarations

let declare_macro mn l f =
  if is_built_in mn then raise Reserved_identifier ;
  if Hashtbl.mem macros mn then raise Multiple_declarations ;
  Hashtbl.add macros mn (l,f) ;
  mn                            (* TODO: refresh if already there *)

let macro_domain mn = fst (Hashtbl.find macros mn)

let macro_declaration mn action indices =
  let l,f =
    if is_built_in mn then
      failwith "look-up of a built-in declaration"
    else Hashtbl.find macros mn
  in
  assert (List.length action = l) ;
  f action indices

let mk_mname mn indices = (mn,indices)

let in_macro = ("input", [])
let out_macro = ("output", [])

type asubst =
  | Term of term * term
  | TS of timestamp * timestamp
  | Index of index * index

type subst = asubst list

exception Substitution_error of string

let pp_asubst ppf e =
  let pp_el pp_t (t1,t2) = Fmt.pf ppf "%a->%a" pp_t t1 pp_t t2 in
  match e with
  | Term(t1, t2) -> pp_el pp_term (t1, t2)
  | TS(ts1, ts2) -> pp_el pp_timestamp (ts1, ts2)
  | Index(i1, i2) -> pp_el Vars.pp (i1, i2)


let pp_subst ppf s =
  Fmt.pf ppf "@[<hv 0>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") pp_asubst) s

let term_subst (s : subst) =
  List.fold_left (fun acc asubst ->
      match asubst with Term(t1, t2) -> (t1, t2)::acc | _ -> acc
    ) [] s

let ts_subst (s : subst) =
  List.fold_left (fun acc asubst ->
      match asubst with TS(t1, t2) -> (t1, t2)::acc | _ -> acc
    ) [] s

let to_isubst (s : subst) =
  List.fold_left (fun acc asubst ->
      match asubst with Index(t1, t2) -> (t1, t2)::acc | _ -> acc
    ) [] s

let rec from_varsubst l =
  match l with
  | [] -> []
  | (t1, t2)::l when (var_type t1 = Timestamp) &&  (var_type t2 = Timestamp) ->
    (TS(TVar t1, TVar t2))::(from_varsubst l)
  | (t1, t2)::l when (var_type t1 = Message) &&  (var_type t2 = Message) ->
    (Term(MVar t1, MVar t2))::(from_varsubst l)
  | (t1, t2)::l when (var_type t1 = Index) &&  (var_type t2 = Index) ->
    (Index(t1, t2))::(from_varsubst l)
  | _ -> failwith "ill-typed substitution"

let get_term_subst (s : subst) (t : term) =
  try
    List.assoc t (term_subst s)
  with Not_found -> t

let get_ts_subst (s : subst) (ts : timestamp) =
  try
    List.assoc ts (ts_subst s)
  with Not_found -> ts

let get_index_subst (s : subst) (i : index) =
  try
    List.assoc i (to_isubst s)
  with Not_found -> i

let subst_index = get_index_subst

let rec subst_action (s : subst) (a : action) =
  match a with
  | [] -> []
  | a :: l ->
    let p,lp = a.par_choice in
    let q,lq = a.sum_choice in
    { par_choice = p, List.map (get_index_subst s) lp ;
      sum_choice = q, List.map (get_index_subst s) lq }
    :: subst_action s l

let subst_state (s : subst) ((st, is) : state) =
  (st, List.map (get_index_subst s) is)

let rec subst_ts (s : subst) (ts : timestamp) =
  let newts =
    (match ts with
     | TVar _ -> ts
     | TPred ts' -> TPred (subst_ts s ts')
     | TName (ac) -> TName (subst_action s ac)
    ) in
  get_ts_subst s newts

let rec subst_term (s : subst) (t : term) =
  let newt =
    match t with
    | Fun (fs, lt) ->Fun (fs, List.map (subst_term s) lt)
    | Name (ns, lt) -> Name (ns, List.map (subst_index s) lt)
    | State (st, ts) -> State (subst_state s st, subst_ts s ts)
    | Macro ((m, idx), ts) ->
      Macro ((m,List.map (subst_index s) idx), subst_ts s ts)
    | MVar _ -> t
  in
  get_term_subst s newt
