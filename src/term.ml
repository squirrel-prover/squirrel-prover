(** Symbols *)

type 'a indexed_symbol = 'a Symbols.t * Vars.index list

type name = Symbols.name Symbols.t
type nsymb = Symbols.name indexed_symbol

type fname = Symbols.fname Symbols.t
type unsupported_index = Vars.index
type fsymb = Symbols.fname Symbols.t * unsupported_index list

type mname = Symbols.macro Symbols.t
type msymb = Symbols.macro indexed_symbol

type state = msymb

let pp_name ppf = function s -> (Utils.kw `Yellow) ppf (Symbols.to_string s)

(* TODO find a better name... pp_name_indices ? *)
let pp_nsymb ppf (n,is) =
  if is <> [] then Fmt.pf ppf "%a(%a)" pp_name n Vars.pp_list is
  else Fmt.pf ppf "%a" pp_name n

let pp_fname ppf s = (Utils.kw `Bold) ppf (Symbols.to_string s)

let pp_fsymb ppf (fn,is) = match is with
  | [] -> Fmt.pf ppf "%a" pp_fname fn
  | _ -> Fmt.pf ppf "%a[%a]" pp_fname fn Vars.pp_list is

let pp_mname ppf s =
  let open Fmt in
  (styled `Bold (styled `Magenta Utils.ident)) ppf (Symbols.to_string s)

let pp_msymb ppf (m,is) =
  Fmt.pf ppf "%a%a"
    pp_mname m
    (Utils.pp_ne_list "(%a)" Vars.pp_list) is

(** Atoms and terms *)

type ord = [ `Eq | `Neq | `Leq | `Geq | `Lt | `Gt ]
type ord_eq = [ `Eq | `Neq ]

type ('a,'b) _atom = 'a * 'b * 'b

type generic_atom = [
  | `Message of (ord_eq,Sorts.message term) _atom
  | `Timestamp of (ord,Sorts.timestamp term) _atom
  | `Index of (ord_eq,Vars.index) _atom
  | `Happens of Sorts.timestamp term
]
and _ term =
  | Fun : fsymb *  Sorts.message term list -> Sorts.message term
  | Name : nsymb -> Sorts.message term
  | Macro :
      msymb * Sorts.message term list * Sorts.timestamp term ->
      Sorts.message term
  | Pred : Sorts.timestamp term -> Sorts.timestamp term
  | Action :
      Symbols.action Symbols.t * Vars.index list ->
      Sorts.timestamp term
  | Init : Sorts.timestamp term
  | Var : 'a Vars.var -> 'a term

  | Diff : 'a term * 'a term -> 'a term
  | Left : 'a term -> 'a term
  | Right : 'a term -> 'a term

  | ITE :
      Sorts.boolean term * Sorts.message term * Sorts.message term ->
      Sorts.message term
  | Find :
      Vars.index list * Sorts.boolean term *
      Sorts.message term * Sorts.message term ->
      Sorts.message term

  | Atom : generic_atom -> Sorts.boolean term


  | ForAll : Vars.evar list * Sorts.boolean term -> Sorts.boolean term
  | Exists : Vars.evar list * Sorts.boolean term -> Sorts.boolean term
  | And : Sorts.boolean term * Sorts.boolean term -> Sorts.boolean term
  | Or : Sorts.boolean term * Sorts.boolean term -> Sorts.boolean term
  | Not : Sorts.boolean term  -> Sorts.boolean term
  | Impl : Sorts.boolean term * Sorts.boolean term -> Sorts.boolean term
  | True : Sorts.boolean term
  | False : Sorts.boolean term

type 'a t = 'a term

type message = Sorts.message term
type timestamp = Sorts.timestamp term
type formula = Sorts.boolean term

type message_atom = [ `Message of ord_eq * message
                               * message ]
type trace_atom = [
  | `Timestamp of (ord,timestamp) _atom
  | `Index of (ord_eq,Vars.index) _atom
]

let rec sort : type a. a term -> a Sorts.t =
  function
  | Fun _ -> Sorts.Message
  | Name _ -> Sorts.Message
  | Macro _ -> Sorts.Message
  | Var v -> Vars.sort v
  | Pred _ -> Sorts.Timestamp
  | Action _ -> Sorts.Timestamp
  | Init -> Sorts.Timestamp
  | Diff (a, b) -> sort a
  | Left a -> sort a
  | Right a -> sort a
  | ITE (a, b, c) -> Sorts.Message
  | Find (a, b, c, d) -> Sorts.Message
  | Atom _ -> Sorts.Boolean
  | ForAll _ -> Sorts.Boolean
  | Exists _ -> Sorts.Boolean
  | And _ -> Sorts.Boolean
  | Or _ -> Sorts.Boolean
  | Not _ -> Sorts.Boolean
  | Impl _ -> Sorts.Boolean
  | True -> Sorts.Boolean
  | False -> Sorts.Boolean

exception Not_a_disjunction

let rec disjunction_to_atom_list = function
  | False -> []
  | Atom at -> [at]
  | Or (a, b) -> disjunction_to_atom_list a @ disjunction_to_atom_list b
  | _ -> raise Not_a_disjunction


let pp_indices ppf l =
  if l <> [] then Fmt.pf ppf "(%a)" Vars.pp_list l

let pp_ord ppf = function
  | `Eq -> Fmt.pf ppf "="
  | `Neq -> Fmt.pf ppf "<>"
  | `Leq -> Fmt.pf ppf "<="
  | `Geq -> Fmt.pf ppf ">="
  | `Lt -> Fmt.pf ppf "<"
  | `Gt -> Fmt.pf ppf ">"

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
  | Init -> Fmt.styled `Green (fun ppf () -> Fmt.pf ppf "init") ppf ()
  | Diff (bl, br) ->
    Fmt.pf ppf "@[<1>(diff(%a, %a))@]"
      pp bl pp br
  | Left b->
    Fmt.pf ppf "@[<1>(left(%a))@]"
      pp b
  | Right b ->
    Fmt.pf ppf "@[<1>(right(%a))@]"
      pp b
  | ITE (b, c, d) ->
    Fmt.pf ppf "@[<1>(if %a then %a else %a)@]"
      pp b pp c pp d
  | Find (b, c, d, e) ->
    Fmt.pf ppf "@[<1>(try find %a such that %a in %a else %a)@]"
      Vars.pp_typed_list (List.map (fun t -> Vars.EVar t) b) pp c pp d pp e
  | ForAll (vs, b) ->
    Fmt.pf ppf "@[forall (@[%a@]),@ %a@]"
      Vars.pp_typed_list vs pp b
  | Exists (vs, b) ->
    Fmt.pf ppf "@[exists (@[%a@]),@ %a@]"
      Vars.pp_typed_list vs pp b
  | And (bl, br) ->
    Fmt.pf ppf "@[<1>(%a@ &&@ %a)@]"
      pp bl pp br
  | Or (bl, br) ->
    Fmt.pf ppf "@[<1>(%a@ ||@ %a)@]"
      pp bl pp br
  | Impl (bl, br) ->
    Fmt.pf ppf "@[<1>(%a@ =>@ %a)@]"
      pp bl pp br
  | Not b ->
    Fmt.pf ppf "not(@[%a@])" pp b
  | Atom a -> pp_generic_atom ppf a
  | True -> Fmt.pf ppf "True"
  | False -> Fmt.pf ppf "False"
and pp_message_atom ppf (`Message (o,tl,tr)) =
  Fmt.pf ppf "@[%a@ %a@ %a@]" pp tl pp_ord o pp tr
and pp_trace_atom ppf : trace_atom -> unit = function
  | `Timestamp (o,tl,tr) ->
    Fmt.pf ppf "@[<hv>%a@ %a@ %a@]" pp tl pp_ord o pp tr
  | `Index (o,il,ir) ->
    Fmt.pf ppf "@[<hv>%a@ %a@ %a@]" Vars.pp il pp_ord o Vars.pp ir
and pp_generic_atom ppf = function
  | `Happens a -> Fmt.pf ppf "happens(%a)" pp a
  | #message_atom as a -> pp_message_atom ppf a
  | #trace_atom as a -> pp_trace_atom ppf a

let get_vars : 'a term -> Vars.evar list =
  fun term ->
  let res = ref [] in
  let rec termvars : type a. a term -> unit =
    function
    | Action (_,indices) ->
        res :=
          List.map (fun x -> Vars.EVar x) indices @
          !res
    | Var tv -> res := Vars.EVar tv :: !res
    | Pred ts -> termvars ts
    | Fun (_, lt) -> List.iter termvars lt
    | Macro (_, l, ts) -> List.iter termvars l; termvars ts
    | Name _ -> ()
    | Init -> ()
    |  _ -> failwith "Not implemented"
  in
  termvars term; !res

(** Declare input and output macros.
  * We assume that they are the only symbols bound to Input/Output. *)
let in_macro = (Symbols.Macro.declare_exact "input" ~builtin:true Symbols.Input, [])
let out_macro = (Symbols.Macro.declare_exact "output" ~builtin:true Symbols.Output, [])

let rec tts acc = function
  | Fun (_, lt) -> List.fold_left tts acc lt
  | Name _ -> acc
  | Macro (_, l, ts) -> List.fold_left tts (ts :: acc) l
  | Var _ -> []
  |  _ -> failwith "Not implemented"

let get_ts t = tts [] t |> List.sort_uniq Pervasives.compare

let rec pts acc = function
  | Fun (_, lt) -> List.fold_left pts acc lt
  | Macro (s, l, ts) ->
     if s = in_macro then (Pred ts) :: acc else
       List.fold_left pts (ts :: acc) l
  | Name _ -> acc
  | Var _ -> []
  |  _ -> failwith "Not implemented"

let precise_ts t = pts [] t |> List.sort_uniq Pervasives.compare

(** Substitutions *)

type esubst = ESubst : 'a term * 'a term -> esubst

type subst = esubst list

exception Uncastable

let cast: type a b. a Sorts.sort -> b term -> a term =
  fun kind t ->
  match kind, sort t with
     | Sorts.Index, Sorts.Index -> t
     | Sorts.Message, Sorts.Message -> t
     | Sorts.Boolean, Sorts.Boolean -> t
     | Sorts.Timestamp, Sorts.Timestamp -> t
     | _ -> raise Uncastable


let rec assoc : type a. subst -> a term -> a term =
  fun subst term ->
  match subst with
  | [] -> term
  | ESubst (t1,t2)::q ->
    try
      let term2 = cast (sort t1) term in
      if term2 = t1 then cast (sort term) t2 else assoc q term
    with Uncastable -> assoc q term

exception Substitution_error of string

let pp_esubst ppf (ESubst (t1,t2)) =
  Fmt.pf ppf "%a->%a" pp t1 pp t2

let pp_subst ppf s =
  Fmt.pf ppf "@[<hv 0>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") pp_esubst) s

let subst_var : type a. subst -> a Vars.var -> a Vars.var =
    fun subst var ->
    match assoc subst (Var var) with
    | Var var -> var
    | _ -> raise @@ Substitution_error
        "Must map the given variable to another variable"

let subst_macro (s:subst) (symb,is) =
  (symb, List.map (subst_var s) is)

let rec subst : type a. subst -> a term -> a term = fun s t ->
  let new_term : a term =
    match t with
    | Fun ((fs,is), lt) ->
      Fun ((fs, List.map (subst_var s) is),
           List.map (subst s) lt)
    | Name (ns,is) -> Name (ns, List.map (subst_var s) is)
    | Macro (m, l, ts) ->
      Macro (subst_macro s m, List.map (subst s) l, subst s ts)
    | Var m -> Var m
    | Pred ts -> Pred (subst s ts)
    | Action (a,indices) -> Action (a, List.map (subst_var s) indices)
    | Init -> Init
    | Diff (a, b) -> Diff (subst s a, subst s b)
    | Left a -> Left (subst s a)
    | Right a -> Right (subst s a)
    | ITE (a, b, c) -> ITE (subst s a, subst s b, subst s c)
    | Atom a-> Atom (subst_generic_atom s a)
    | And (a, b) -> And (subst s a, subst s b)
    | Or (a, b) -> Or (subst s a, subst s b)
    | Not a -> Not (subst s a)
    | Impl (a, b) -> Impl (subst s a, subst s b)
    | True -> True
    | False -> False
    (** Warning - TODO - the substititution is currently propagated without any
       check. Cf #71. *)
    | ForAll (a, b) -> ForAll (a, subst s b)
    | Exists (a, b) -> Exists (a, subst s b)
    | Find (a, b, c, d) ->
        Find ((List.map (subst_var s) a), subst s b, subst s c, subst s d)
  in
  assoc s new_term

and subst_message_atom (s : subst) (`Message (ord, a1, a2)) =
  `Message (ord, subst s a1, subst s a2)

and subst_trace_atom (s:subst) = function
  | `Timestamp (ord, ts, ts') ->
    `Timestamp (ord, subst s ts, subst s ts')
  | `Index (ord, i, i') ->
    `Index(ord, subst_var s i,subst_var s i')
and subst_generic_atom s = function
  | `Happens a -> `Happens (subst s a)
  | #message_atom as a -> (subst_message_atom s a :> generic_atom)
  | #trace_atom as a -> (subst_trace_atom s a :> generic_atom)



(** Builtins *)

let mk_fname ?(indices=0) f k_args k_ret =
  let info = indices, Symbols.Abstract (k_args,k_ret) in
  Symbols.Function.declare_exact f ~builtin:true info, []

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

(** Pairing *)

let f_pair = mk_fname "pair" [emessage;emessage] emessage
let f_fst = mk_fname "fst" [emessage] emessage
let f_snd = mk_fname "snd" [emessage] emessage

(** Dummy term *)

let dummy = Fun (mk_fname "_" [] emessage, [])

type projection = Left | Right

let rec pi_term : type a. projection -> a term -> a term =
  fun s t ->
  match t with
  | Fun (f,terms) -> Fun (f, List.map (pi_term s) terms)
  | Name n -> Name n
  | Macro (m, terms, ts) -> Macro(m, List.map (pi_term s) terms, (pi_term s ts))
  | Pred t -> Pred (pi_term s t)
  | Action (a, b) -> Action (a, b)
  | Init -> Init
  | Var a -> Var a
  | Diff (a, b) ->
    begin
      match s with
      | Left -> pi_term s a
      | Right -> pi_term s b
    end
  | Left a -> pi_term Left a
  | Right a -> pi_term Right a
  | ITE (a, b, c) -> ITE (pi_term s a, pi_term s b, pi_term s c)
  | Find (vs, b, t, e) -> Find (vs, pi_term s b, pi_term s t, pi_term s e)
  | ForAll (vs, b) -> ForAll (vs, pi_term s b)
  | Exists (vs, b) -> Exists (vs, pi_term s b)
  | And (a, b) -> And (pi_term s a, pi_term s b)
  | Or (a, b) -> Or (pi_term s a, pi_term s b)
  | Not a -> Not (pi_term s a)
  | Impl (a, b) -> Impl (pi_term s a, pi_term s b)
  | True -> True
  | False -> False
  | Atom a -> Atom (pi_generic_atom s a)

and pi_generic_atom s =
  function
   | `Message  (o,t1,t2) -> `Message (o, pi_term s t1, pi_term s t2)
   | `Timestamp (o, ts1, ts2) -> `Timestamp (o, pi_term s ts1, pi_term s ts2)
   | `Index (o, i1, i2) as r -> r
   | `Happens t -> `Happens (pi_term s t)

let rec head_pi_term : type a. projection -> a term -> a term =
  fun s t ->
  match t with
  | Diff (a, b) ->
    begin
      match s with
      | Left -> head_pi_term s a
      | Right -> head_pi_term s b
    end
  | Left t -> head_pi_term Left t
  | Right t -> head_pi_term Right t
  |  _ -> t

let diff a b = Diff (a,b)

(* We ignore the possibility of diff operators on indices and timestamps. *)
let head_normal_biterm : type a. a term -> a term = fun t ->
  match head_pi_term Left t, head_pi_term Right t with
  | Fun (f,l), Fun (f',l') when f=f' -> Fun (f, List.map2 diff l l')
  | Name n, Name n' when n=n' -> Name n
  | Macro (m,l,ts), Macro (m',l',ts') when m=m' && ts=ts' ->
      Macro (m, List.map2 diff l l', ts)
  | Pred t, Pred t' -> Pred (Diff (t,t'))
  | Action (a,is), Action (a',is') when a=a' && is=is' -> Action (a,is)
  | Init, Init -> Init
  | Var x, Var x' when x=x' -> Var x
  | ITE (i,t,e), ITE (i',t',e') -> ITE (Diff (i,i'), Diff (t,t'), Diff (e,e'))
  | Find (is,c,t,e), Find (is',c',t',e') when is=is' ->
      Find (is,Diff (c,c'), Diff (t,t'), Diff (e,e'))
  | Atom a, Atom a' when a=a' -> Atom a
  | Atom (`Message (o,u,v)), Atom (`Message (o',u',v')) when o=o' ->
      Atom (`Message (o, Diff (u,u'), Diff (v,v')))
  | ForAll (vs,f), ForAll (vs',f') when vs=vs' ->
      ForAll (vs,Diff (f,f'))
  | Exists (vs,f), Exists (vs',f') when vs=vs' ->
      Exists (vs,Diff (f,f'))
  | And (f,g), And (f',g') -> And (Diff (f,g), Diff (f',g'))
  | Or (f,g), Or (f',g') -> Or (Diff (f,g), Diff (f',g'))
  | Impl (f,g), Impl (f',g') -> Impl (Diff (f,g), Diff (f',g'))
  | Not f, Not f' -> Not (Diff (f,f'))
  | True, True -> True
  | False, False -> False
  | t1,t2 -> Diff (t1,t2)
