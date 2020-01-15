type 'a indexed_symbol = 'a Symbols.t * Vars.index list

type name = Symbols.name Symbols.t
type nsymb = Symbols.name indexed_symbol

type fname = Symbols.fname Symbols.t
type fsymb = Symbols.fname indexed_symbol

type mname = Symbols.macro Symbols.t
type msymb = Symbols.macro indexed_symbol

type state = msymb


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

type _ term =
  | Fun : fsymb *  Sorts.message term list -> Sorts.message term
  | Name : nsymb -> Sorts.message term
  | Macro :  msymb * Sorts.message term list * Sorts.timestamp term
      -> Sorts.message term
  | Pred : Sorts.timestamp term -> Sorts.timestamp term
  | Action : Symbols.action Symbols.t * Vars.index list -> Sorts.timestamp term
  | Var : 'a Vars.var -> 'a term

type 'a t = 'a term

type message = Sorts.message term
type timestamp = Sorts.timestamp term

let pp_indices ppf l =
  if l <> [] then Fmt.pf ppf "(%a)" Vars.pp_list l

let rec pp : type a. Format.formatter -> a term -> unit = fun ppf -> function
  | Var m -> Fmt.pf ppf "%a" Vars.pp m
  | Fun ((s,[]),terms) when Symbols.to_string s = "pair" ->
      Fmt.pf ppf "%a"
        (Utils.pp_ne_list
           "<@[<hov>%a@]>"
           (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,") pp)) terms
  | Fun (f,terms) ->
      Fmt.pf ppf "%a%a"
        pp_fsymb f
        (Utils.pp_ne_list
           "(@[<hov>%a@])"
           (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,") pp)) terms
  | Name n -> pp_nsymb ppf n
  | Macro (m, l, ts) ->
      Fmt.pf ppf "@[%a%a@%a@]"
        pp_msymb m
        (Utils.pp_ne_list
           "(@[<hov>%a@])"
           (Fmt.list ~sep:Fmt.comma pp)) l
        pp ts
  | Pred ts -> Fmt.pf ppf "@[<hov>pred(%a)@]" pp ts
  | Action (symb,indices) ->
      Fmt.styled `Green
        (fun ppf () ->
           Fmt.pf ppf "%s%a" (Symbols.to_string symb) pp_indices indices)
        ppf ()


let rec termvars : type a. Vars.evar list -> a term -> Vars.evar list = fun vs t ->
    match t with
  | Action (_,indices) -> (List.map (fun x -> Vars.EVar x) indices) @ vs
  | Var tv -> Vars.EVar tv :: vs
  | Pred ts -> termvars vs ts
  | Fun (fs, lt) -> List.fold_left (fun vs t -> termvars vs t) vs lt
  | Name n -> vs
  | Macro (_, l, ts) -> termvars
                          (List.fold_left (fun vs t -> termvars vs t) vs l) ts

let get_vars = termvars []


(** Declare input and output macros.
  * We assume that they are the only symbols bound to Input/Output. *)
let in_macro = (Symbols.Macro.declare_exact "input" Symbols.Input, [])
let out_macro = (Symbols.Macro.declare_exact "output" Symbols.Output, [])

let rec tts acc = function
  | Fun (fs, lt) -> List.fold_left tts acc lt
  | Name n -> acc
  | Macro (_, l, ts) -> List.fold_left tts (ts :: acc) l
  | Var _ -> []

let get_ts t = tts [] t |> List.sort_uniq Pervasives.compare

let rec pts acc = function
  | Fun (fs, lt) -> List.fold_left pts acc lt
  | Macro (s, l, ts) ->
     if s = in_macro then (Pred ts) :: acc else
       List.fold_left pts (ts :: acc) l
  | Name n -> acc
  | Var _ -> []

let precise_ts t = pts [] t |> List.sort_uniq Pervasives.compare

(** Substitutions *)

type esubst = ESubst : 'a Vars.var * 'a term -> esubst

type subst = esubst list

let cast : type a b. a Sorts.t -> b Sorts.t -> a term -> b term  =
  fun v var t ->
  match v, var with
     | Sorts.Index, Sorts.Index -> t
     | Sorts.Message, Sorts.Message -> t
     | Sorts.Boolean, Sorts.Boolean -> t
     | Sorts.Timestamp, Sorts.Timestamp -> t
     | _ -> assert false

let rec assoc (subst:subst) (var:'a Vars.var) =
  match subst with
  | [] -> Var var
  | ESubst (v,t)::q when Vars.EVar v = Vars.EVar var->
    cast (Vars.var_type v) (Vars.var_type var) t
  | p::q -> assoc q var

exception Substitution_error of string

let pp_esubst ppf (ESubst (v,t)) =
  Fmt.pf ppf "%a->%a" Vars.pp v pp t

let pp_subst ppf s =
  Fmt.pf ppf "@[<hv 0>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") pp_esubst) s

let rec subst_var (subst:subst) (var:'a Vars.var) =
  match assoc subst var with
  | Var var -> var
  | _ -> raise @@ Substitution_error
      "Must map the given variable to another variable"

let subst_macro (s:subst) (symb,is) =
  (symb, List.map (subst_var s) is)

let rec subst : type a. subst -> a term -> a term = fun s t ->
  match t with
    | Fun ((fs,is), lt) ->
        Fun ((fs, List.map (subst_var s) is),
             List.map (subst s) lt)
    | Name (ns,is) -> Name (ns, List.map (subst_var s) is)
    | Macro (m, l, ts) ->
        Macro (subst_macro s m, List.map (subst s) l, subst s ts)
    | Var m -> assoc s m
    | Pred ts -> Pred (subst s ts)
    | Action (a,indices) -> Action (a, List.map (subst_var s) indices)

(** Builtins *)

let mk_fname ?(indices=0) f k_args k_ret =
  let info = indices, Symbols.Abstract (k_args,k_ret) in
  Symbols.Function.declare_exact f info, []

(** Boolean function symbols *)
open Sorts
let f_false = mk_fname "false" [] eboolean
let f_true = mk_fname "true" [] eboolean
let f_and = mk_fname "and" [eboolean;eboolean] eboolean
let f_or = mk_fname "or" [eboolean;eboolean] eboolean
let f_not = mk_fname "not" [eboolean] eboolean
let f_ite = mk_fname "if" [eboolean;emessage;emessage] emessage

(** Xor and its unit *)

let f_xor = mk_fname "xor" [emessage;emessage] emessage
let f_zero = mk_fname "zero" [] emessage

(** Successor over natural numbers *)

let f_succ = mk_fname "succ" [emessage] emessage

(** Operations on timestamps *)

let f_pred = mk_fname "pred" [etimestamp] etimestamp

(** Pairing *)

let f_pair = mk_fname "pair" [emessage;emessage] emessage
let f_fst = mk_fname "fst" [emessage] emessage
let f_snd = mk_fname "snd" [emessage] emessage

(** Dummy term *)

let dummy = Fun (mk_fname "_" [] emessage, [])
