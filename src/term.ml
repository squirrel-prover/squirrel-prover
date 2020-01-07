open Vars

type timestamp =
  | TVar of var
  | TPred of timestamp
  | TName of Symbols.action Symbols.t * Index.t list

let pp_indices ppf l =
  if l <> [] then Fmt.pf ppf "(%a)" Vars.pp_list l

let rec pp_timestamp ppf = function
  | TVar tv -> Vars.pp ppf tv
  | TPred ts -> Fmt.pf ppf "@[<hov>pred(%a)@]" pp_timestamp ts
  | TName (symb,indices) ->
      Fmt.styled `Green
        (fun ppf () ->
           Fmt.pf ppf "%s%a" (Symbols.to_string symb) pp_indices indices)
        ppf ()

let rec tsvars vs = function
  | TVar tv -> tv :: vs
  | TName (_,indices) -> indices @ vs
  | TPred ts -> tsvars vs ts

let ts_vars = tsvars []

type mvar = Vars.var

(** Symbols *)

type kind = Vars.sort

type 'a indexed_symbol = 'a Symbols.t * Index.t list

type name = Symbols.name Symbols.t
type nsymb = Symbols.name indexed_symbol

type fname = Symbols.fname Symbols.t
type fsymb = Symbols.fname indexed_symbol

type mname = Symbols.macro Symbols.t
type msymb = Symbols.macro indexed_symbol

type state = msymb

(** Type of terms, parameterized by the type of the macro namespace *)
type term =
  | Fun of fsymb * term list
  | Name of nsymb
  | MVar of var
  | Macro of msymb * term list * timestamp

(** Declare input and output macros.
  * We assume that they are the only symbols bound to Input/Output. *)
let in_macro = (Symbols.Macro.declare_exact "input" Symbols.Input, [])
let out_macro = (Symbols.Macro.declare_exact "output" Symbols.Output, [])

(** Pretty printing *)

let pp_name ppf = function s -> (Utils.kw `Yellow) ppf (Symbols.to_string s)

(* TODO find a better name... pp_name_indices ? *)
let pp_nsymb ppf (n,is) =
  if is <> [] then Fmt.pf ppf "%a(%a)" pp_name n Vars.pp_list is
  else Fmt.pf ppf "%a" pp_name n

let pp_fname ppf s = (Utils.kw `Bold) ppf (Symbols.to_string s)

let pp_fsymb ppf (fn,is) = match is with
  | [] -> Fmt.pf ppf "%a" pp_fname fn
  | _ -> Fmt.pf ppf "%a[%a]" pp_fname fn Vars.pp_list is

let pp_sname ppf s = (Utils.kw `Red) ppf (Symbols.to_string s)

let pp_mname ppf s =
  let open Fmt in
  (styled `Bold (styled `Magenta Utils.ident)) ppf (Symbols.to_string s)

let pp_msymb ppf (m,is) =
  Fmt.pf ppf "%a%a"
    pp_mname m
    (Utils.pp_ne_list "(%a)" Vars.pp_list) is

let rec pp_term ppf = function
  | Fun ((s,[]),terms) when Symbols.to_string s = "pair" ->
      Fmt.pf ppf "%a"
        (Utils.pp_ne_list
           "<@[<hov>%a@]>"
           (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,") pp_term)) terms
  | Fun (f,terms) ->
      Fmt.pf ppf "%a%a"
        pp_fsymb f
        (Utils.pp_ne_list
           "(@[<hov>%a@])"
           (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,") pp_term)) terms
  | Name n -> pp_nsymb ppf n
  | Macro (m, l, ts) ->
      Fmt.pf ppf "@[%a%a@%a@]"
        pp_msymb m
        (Utils.pp_ne_list
           "(@[<hov>%a@])"
           (Fmt.list ~sep:Fmt.comma pp_term)) l
        pp_timestamp ts
  | MVar m -> Fmt.pf ppf "%a" Vars.pp m

let rec tvars acc = function
  | Fun ((_, is) , lt) -> List.fold_left tvars (is@acc) lt
  | Name (_, is) ->  is@acc
  | Macro ((_, is), l, ts) -> List.fold_left tvars (tsvars (is@acc) ts) l
  | MVar _ ->  []

let term_vars t =
  tvars [] t
  |> List.sort_uniq Pervasives.compare

let rec tts acc = function
  | Fun (fs, lt) -> List.fold_left tts acc lt
  | Name n -> acc
  | Macro (_, l, ts) -> List.fold_left tts (ts :: acc) l
  | MVar _ -> []

let term_ts t = tts [] t |> List.sort_uniq Pervasives.compare

let rec pts acc = function
  | Fun (fs, lt) -> List.fold_left pts acc lt
  | Macro (s, l, ts) ->
     if s = in_macro then (TPred ts) :: acc else
       List.fold_left pts (ts :: acc) l
  | Name n -> acc
  | MVar _ -> []

let precise_ts t = pts [] t |> List.sort_uniq Pervasives.compare

(** Substitutions *)

type asubst =
  | Term of term * term
  | TS of timestamp * timestamp
  | Index of Index.t * Index.t

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

let get_index_subst (s : subst) (i : Index.t) =
  try
    List.assoc i (to_isubst s)
  with Not_found -> i

let subst_index = get_index_subst

let subst_macro (s:subst) (symb,is) =
  (symb, List.map (get_index_subst s) is)

let rec subst_ts (s : subst) (ts : timestamp) =
  let newts =
    (match ts with
     | TVar _ -> ts
     | TPred ts' -> TPred (subst_ts s ts')
     | TName (a,indices) -> TName (a, List.map (subst_index s) indices)
    ) in
  get_ts_subst s newts

let rec subst_term (s : subst) (t : term) =
  match t with
    | Fun ((fs,is), lt) ->
        Fun ((fs, List.map (subst_index s) is),
             List.map (subst_term s) lt)
    | Name (ns,is) -> Name (ns, List.map (subst_index s) is)
    | Macro (m, l, ts) ->
        Macro (subst_macro s m, List.map (subst_term s) l, subst_ts s ts)
    | MVar _ -> get_term_subst s t

(** Builtins *)

let mk_fname ?(indices=0) f k_args k_ret =
  let info = indices, Symbols.Abstract (k_args,k_ret) in
  Symbols.Function.declare_exact f info, []

(** Boolean function symbols *)

let f_false = mk_fname "false" [] Boolean
let f_true = mk_fname "true" [] Boolean
let f_and = mk_fname "and" [Boolean;Boolean] Boolean
let f_or = mk_fname "or" [Boolean;Boolean] Boolean
let f_not = mk_fname "not" [Boolean] Boolean
let f_ite = mk_fname "if" [Boolean;Message;Message] Message

(** Xor and its unit *)

let f_xor = mk_fname "xor" [Message;Message] Message
let f_zero = mk_fname "zero" [] Message

(** Successor over natural numbers *)

let f_succ = mk_fname "succ" [Message] Message

(** Operations on timestamps *)

let f_pred = mk_fname "pred" [Timestamp] Timestamp

(** Pairing *)

let f_pair = mk_fname "pair" [Message;Message] Message
let f_fst = mk_fname "fst" [Message] Message
let f_snd = mk_fname "snd" [Message] Message

(** Dummy term *)

let dummy = Fun (mk_fname "_" [] Message, [])
