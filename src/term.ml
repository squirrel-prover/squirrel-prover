
(** Symbols *)

type 'a indexed_symbol = 'a * Vars.index list

type name = Symbols.name Symbols.t
type nsymb = name indexed_symbol

type fname = Symbols.fname Symbols.t
type fsymb = fname * Vars.index list

type mname = Symbols.macro Symbols.t
type 'a msymb = mname * 'a Sorts.sort * Vars.index list

type state = Sorts.message msymb

let pp_name ppf = function s -> (Utils.kw `Yellow) ppf (Symbols.to_string s)

let pp_nsymb ppf (n,is) =
  if is <> [] then Fmt.pf ppf "%a(%a)" pp_name n Vars.pp_list is
  else Fmt.pf ppf "%a" pp_name n

let pp_fname ppf s = (Utils.kw `Bold) ppf (Symbols.to_string s)

let pp_fsymb ppf (fn,is) = match is with
  | [] -> Fmt.pf ppf "%a" pp_fname fn
  | _ -> Fmt.pf ppf "%a(%a)" pp_fname fn Vars.pp_list is

let pp_mname ppf s =
  let open Fmt in
  (styled `Bold (styled `Magenta Utils.ident)) ppf (Symbols.to_string s)

let pp_msymb ppf (m,s,is) =
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
      'a msymb * Sorts.message term list * Sorts.timestamp term ->
      'a term
  | Seq : Vars.index list * Sorts.message term -> Sorts.message term
  | Pred : Sorts.timestamp term -> Sorts.timestamp term
  | Action :
      Symbols.action Symbols.t * Vars.index list ->
      Sorts.timestamp term
  | Init : Sorts.timestamp term
  | Var : 'a Vars.var -> 'a term

  | Diff : 'a term * 'a term -> 'a term

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
  | Macro ((_,s,_),_,_) -> s
  | Seq _ -> Sorts.Message
  | Var v -> Vars.sort v
  | Pred _ -> Sorts.Timestamp
  | Action _ -> Sorts.Timestamp
  | Init -> Sorts.Timestamp
  | Diff (a, b) -> sort a
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


(** Builtins *)

let mk_fname f arity =
  let info = 0, Symbols.Abstract arity in
  snd
    (Symbols.Function.declare_exact Symbols.dummy_table f ~builtin:true info),
  []

let f_diff = mk_fname "diff" 2

(** Boolean function symbols, where booleans are typed as messages.
  * The true/false constants are used in message_of_formula,
  * and other symbols are used in an untyped way in Completion
  * (in some currently unused code). *)

let eboolean,emessage = Sorts.eboolean,Sorts.emessage

let f_false = mk_fname "false" 0
let f_true = mk_fname "true" 0
let f_and = mk_fname "and" 2
let f_or = mk_fname "or" 2
let f_not = mk_fname "not" 1
let f_ite = mk_fname "if" 3

(** Xor and its unit *)

let f_xor = mk_fname "xor" 2
let f_zero = mk_fname "zero" 0

(** Successor over natural numbers *)

let f_succ = mk_fname "succ" 1

(** Pairing *)

let f_pair = mk_fname "pair" 2
let f_fst = mk_fname "fst" 1
let f_snd = mk_fname "snd" 1

(** Exp **)

let f_exp = mk_fname "exp" 2
let f_g = mk_fname "g" 0

(** Dummy term *)

let dummy = Fun (mk_fname "_" 0, [])

(** Length *)

let f_len = mk_fname "len" 1

(** Convert a boolean term to a message term, used in frame macro definition **)

let boolToMessage b = ITE (b,Fun (f_true,[]),Fun (f_false,[]))

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
  | Fun ((s,[]),[t1;t2]) when Symbols.to_string s = "exp" ->
    Fmt.pf ppf "%a^%a" pp t1 pp t2
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
  | Seq (vs, b) ->
    Fmt.pf ppf "@[seq(@[%a->%a@])@]"
      Vars.pp_list vs pp b
  | Pred ts -> Fmt.pf ppf "@[<hov>pred(%a)@]" pp ts
  | Action (symb,indices) ->
      Fmt.styled `Green
        (fun ppf () ->
           Fmt.pf ppf "%s%a" (Symbols.to_string symb) pp_indices indices)
        ppf ()
  | Init -> Fmt.styled `Green (fun ppf () -> Fmt.pf ppf "init") ppf ()
  | Diff (bl, br) ->
    Fmt.pf ppf "@[<1>diff(%a,@,%a)@]"
      pp bl pp br
  | ITE (b, c, d) ->
    if d = Fun (f_zero,[]) then
      Fmt.pf ppf "@[<3>(if@ %a@ then@ %a)@]"
        pp b pp c
    else if (c = Fun (f_true,[]) && d = Fun (f_false,[])) then
      Fmt.pf ppf "%a" pp b
    else
      Fmt.pf ppf "@[<3>(if@ %a@ then@ %a@ else@ %a)@]"
        pp b pp c pp d
  | Find (b, c, d, e) ->
    if e = Fun (f_zero,[]) then
      Fmt.pf ppf "@[<3>(try find %a such that@ %a@ in@ %a)@]"
        Vars.pp_list b pp c pp d
    else
      Fmt.pf ppf "@[<3>(try find %a such that@ %a@ in@ %a@ else@ %a)@]"
        Vars.pp_list b pp c pp d pp e
  | ForAll (vs, b) ->
    Fmt.pf ppf "@[forall (@[%a@]),@ %a@]"
      Vars.pp_typed_list vs pp b
  | Exists (vs, b) ->
    Fmt.pf ppf "@[exists (@[%a@]),@ %a@]"
      Vars.pp_typed_list vs pp b
  | And (Impl (bl1,br1), Impl(br2,bl2)) when bl1=bl2 && br1=br2 ->
    Fmt.pf ppf "@[<1>(%a@ <=>@ %a)@]"
      pp bl1 pp br1
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


(** Declare input and output macros.
  * TODO this should be moved to the builtin symbol table in Symbols.
  * We assume that they are the only symbols bound to Input/Output. *)
let in_macro = (snd (Symbols.Macro.declare_exact Symbols.dummy_table
                       "input" ~builtin:true
                       Symbols.Input),
                Sorts.Message,
                [])
let out_macro = (snd (Symbols.Macro.declare_exact Symbols.dummy_table
                        "output" ~builtin:true
                        Symbols.Output),
                 Sorts.Message,
                 [])

let cond_macro = (snd (Symbols.Macro.declare_exact Symbols.dummy_table
                         "cond" ~builtin:true
                         Symbols.Cond),
                 Sorts.Boolean,
                 [])

let exec_macro = (snd (Symbols.Macro.declare_exact Symbols.dummy_table
                         "exec" ~builtin:true
                         Symbols.Exec),
                 Sorts.Boolean,
                 [])

let frame_macro = (snd (Symbols.Macro.declare_exact Symbols.dummy_table
                          "frame" ~builtin:true
                          Symbols.Frame),
                   Sorts.Message,
                   [])

let rec pts : type a. timestamp list -> a term -> timestamp list = fun acc -> function
  | Fun (_, lt) -> List.fold_left pts acc lt
  | Macro (s, l, ts) ->
     if Obj.magic s = in_macro then (Pred ts) :: acc else
       List.fold_left pts (ts :: acc) l
  | Name _ -> acc
  | Var _ -> []
  | ITE (f,t,e) -> List.fold_left pts (pts acc f) [t;e]
  | _ -> failwith "Not implemented"

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

let subst_macro (s:subst) (symb, sort, is) =
  (symb, sort, List.map (subst_var s) is)


module S = struct
  include Set.Make(
  struct
    type t = Vars.evar
    let compare (Vars.EVar a) (Vars.EVar b) =
      compare (Vars.name a) (Vars.name b)
  end)
  let add_list vars indices =
    List.fold_left (fun vars i -> add (Vars.EVar i) vars) vars indices
end

let get_set_vars : 'a term -> S.t =
  fun term ->

  let rec termvars : type a. a term -> S.t -> S.t = fun t vars -> match t with
    | Action (_,indices) -> S.add_list vars indices
    | Var tv -> S.add (Vars.EVar tv) vars
    | Pred ts -> termvars ts vars
    | Fun ((_,indices), lt) ->
        let vars = S.add_list vars indices in
        List.fold_left (fun vars x -> termvars x vars) vars lt

    | Macro ((_,_,indices), l, ts) ->
      let vars = S.add_list vars indices in
      termvars ts (List.fold_left (fun vars x -> termvars x vars) vars l)
    | Seq (a, b) ->
      S.diff
        (termvars b vars)
        (S.of_list (List.map (fun x -> Vars.EVar x) a))
    | Name (_,indices) -> S.add_list vars indices
    | Init -> vars
    | Diff (a, b) -> termvars a (termvars b vars)
    | ITE (a, b, c) -> termvars a (termvars b (termvars c vars))
    | Find (a, b, c, d) ->
      S.diff
        (termvars b (termvars c (termvars d vars)))
        (S.of_list (List.map (fun x -> Vars.EVar x) a))
    | Atom a -> generic_atom_vars a vars
    | ForAll (a, b) -> S.diff (termvars b vars) (S.of_list a)
    | Exists (a, b) -> S.diff (termvars b vars) (S.of_list a)
    | And (a, b) ->  termvars a (termvars b vars)
    | Or (a, b) ->  termvars a (termvars b vars)
    | Not a -> termvars a vars
    | Impl (a, b) ->  termvars a (termvars b vars)
    | True -> vars
    | False -> vars

  and message_atom_vars (`Message (ord, a1, a2)) vars =
   termvars a1 (termvars a2 vars)

  and trace_atom_vars at vars = match at with
    | `Timestamp (ord, ts, ts') ->
      termvars ts (termvars ts' vars)
    | `Index (ord, i, i') ->
      termvars (Var i) (termvars (Var i') vars)

  and generic_atom_vars t vars = match t with
    | `Happens a -> termvars a vars
    | #message_atom as a -> message_atom_vars a vars
    | #trace_atom as a -> trace_atom_vars a vars


  in
  termvars term S.empty

let get_vars t = get_set_vars t |> S.elements

let rec subst : type a. subst -> a term -> a term = fun s t ->
  (* given a variable list and a subst s, remove from subst all
     substitution x->v where x is in the variable list. *)
  let filter_subst (vars:Vars.evar list) (s:subst) =
    List.fold_left (fun acc (ESubst (x, y)) ->
        if S.is_empty (S.inter
                         (S.of_list vars)
                         (S.union (get_set_vars x) (get_set_vars y)))
        then
          (ESubst (x, y))::acc
        else
          acc)
      [] s
  in
  (* given a list of variables vars, a substitution s, and a formula f, if some
     var in vars appears in the right hand side of the variables s, we refresh
     the variable and refresh the formula with the new variables. *)
  let refresh_formula vars s f =
    let right_vars = List.fold_left
        (fun acc  (ESubst (x, y)) -> S.union acc (get_set_vars y))  S.empty s
    in
    let all_vars = List.fold_left
        (fun acc  (ESubst (x, y)) -> S.union acc (get_set_vars x))  right_vars s
    in
    let env = Vars.of_list (S.elements all_vars) in
    let v, f = List.fold_left
     (fun  (nvars,f) (Vars.EVar v) ->
            if S.mem (Vars.EVar v) right_vars then
              let new_v = snd (Vars.make_fresh_from env v) in
              ((Vars.EVar new_v)::nvars, subst [ESubst (Var v,Var new_v)] f)
            else
              ((Vars.EVar v)::nvars,f)
     )

      ([],f)
      vars
    in
    List.rev v, f
  in
  let new_term : a term =
    match t with
    | Fun ((fs,is), lt) ->
      Fun ((fs, List.map (subst_var s) is),
           List.map (subst s) lt)
    | Name (ns,is) -> Name (ns, List.map (subst_var s) is)
    | Macro (m, l, ts) ->
      Macro (subst_macro s m, List.map (subst s) l, subst s ts)
    | Seq (a, b) ->
      let s = filter_subst (List.map (fun x -> Vars.EVar x) a) s in
      Seq (a, subst s b)
    | Var m -> Var m
    | Pred ts -> Pred (subst s ts)
    | Action (a,indices) -> Action (a, List.map (subst_var s) indices)
    | Init -> Init
    | Diff (a, b) -> Diff (subst s a, subst s b)
    | ITE (a, b, c) -> ITE (subst s a, subst s b, subst s c)
    | Atom a-> Atom (subst_generic_atom s a)
    | And (a, b) -> And (subst s a, subst s b)
    | Or (a, b) -> Or (subst s a, subst s b)
    | Not a -> Not (subst s a)
    | Impl (a, b) -> Impl (subst s a, subst s b)
    | True -> True
    | False -> False
    | ForAll (a, b) ->
      let filtered_s = filter_subst a s in
      let new_a, new_b = refresh_formula a filtered_s b in
      ForAll (new_a, subst filtered_s new_b)
    | Exists (a, b) ->
      let filtered_s = filter_subst a s in
      let new_a, new_b = refresh_formula a filtered_s b in
      Exists (new_a, subst filtered_s new_b)
    | Find (a, b, c, d) ->
      let ea = List.map (fun x -> Vars.EVar x) a in
      let filtered_s = filter_subst ea s in
      let new_ea, new_b = refresh_formula ea filtered_s b in
      let new_ea, new_c = refresh_formula ea filtered_s c in
      let new_ea, new_d = refresh_formula ea filtered_s d in
      let final_a = List.map (fun (Vars.EVar x) ->
          match Vars.sort x  with
          | Sorts.Index -> (x :> Vars.index)
          | _ -> assert false
        )
         new_ea in
      Find (final_a, subst filtered_s new_b, subst filtered_s new_c,
            subst filtered_s new_d)
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

(** Smart constructors for boolean terms. *)

let mk_not t1 = match t1 with
  | Not t -> t
  | t -> Not t

let mk_and t1 t2 = match t1,t2 with
  | True, t | t, True -> t
  | t1,t2 -> And (t1,t2)

let mk_or t1 t2 = match t1,t2 with
  | False, t | t, False -> t
  | t1,t2 -> Or (t1,t2)

let mk_impl t1 t2 = match t1,t2 with
  | False, _ -> True
  | True, t -> t
  | t1,t2 -> Impl (t1,t2)

let mk_ite c t e = match c with
  | True -> t
  | False -> e
  | _ -> ITE (c,t,e)

let mk_forall l f = if l = [] then f else ForAll (l,f)
let mk_exists l f = if l = [] then f else Exists (l,f)

let message_of_formula f =
  ITE (f, Fun (f_true,[]), Fun (f_false,[]))

let mk_timestamp_leq t1 t2 = match t1,t2 with
  | _, Pred t2' -> `Timestamp (`Lt, t1, t2')
  | _ -> `Timestamp (`Leq, t1, t2)

(** Operations on vectors of indices of the same length. *)
let mk_indices_neq vect_i vect_j =
  List.fold_left
    (fun acc e -> mk_or acc e)
    False
    (List.map2 (fun i j -> Atom (`Index (`Neq, i, j))) vect_i vect_j)
let mk_indices_eq vect_i vect_j =
  List.fold_left
    (fun acc e -> mk_and acc e)
    True
    (List.map2 (fun i j -> Atom (`Index (`Eq, i, j))) vect_i vect_j)

(** Projection *)

type projection = Left | Right | None

let pi_term ~projection term =

  let rec pi_term : type a. projection -> a term -> a term = fun s t ->
  match t with
  | Fun (f,terms) -> Fun (f, List.map (pi_term s) terms)
  | Name n -> Name n
  | Macro (m, terms, ts) -> Macro(m, List.map (pi_term s) terms, pi_term s ts)
  | Seq (a, b) -> Seq (a, pi_term s b)
  | Pred t -> Pred (pi_term s t)
  | Action (a, b) -> Action (a, b)
  | Init -> Init
  | Var a -> Var a
  | Diff (a, b) ->
    begin
      match s with
      | Left -> pi_term s a
      | Right -> pi_term s b
      | None -> Diff (a, b)
    end
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

  and pi_generic_atom s = function
   | `Message  (o,t1,t2) -> `Message (o, pi_term s t1, pi_term s t2)
   | `Timestamp (o, ts1, ts2) -> `Timestamp (o, pi_term s ts1, pi_term s ts2)
   | `Index (o, i1, i2) as r -> r
   | `Happens t -> `Happens (pi_term s t)

  in pi_term projection term

let rec head_pi_term : type a. projection -> a term -> a term =
  fun s t ->
  match t,s with
  | Diff (t,_), Left
  | Diff (_,t), Right -> head_pi_term s t
  | _ -> t

let diff a b =
  let a = match a with Diff (a,_) | a -> a in
  let b = match b with Diff (_,b) | b -> b in
  if a = b then a else Diff (a,b)

let head_normal_biterm : type a. a term -> a term = fun t ->
  match head_pi_term Left t, head_pi_term Right t with
  | Fun (f,l), Fun (f',l') when f=f' -> Fun (f, List.map2 diff l l')
  | Name n, Name n' when n=n' -> Name n
  | Macro (m,l,ts), Macro (m',l',ts') when m=m' && ts=ts' ->
      Macro (m, List.map2 diff l l', ts)
  | Pred t, Pred t' -> Pred (diff t t')
  | Action (a,is), Action (a',is') when a=a' && is=is' -> Action (a,is)
  | Init, Init -> Init
  | Var x, Var x' when x=x' -> Var x
  | ITE (i,t,e), ITE (i',t',e') -> ITE (diff i i', diff t t', diff e e')
  | Find (is,c,t,e), Find (is',c',t',e') when is=is' ->
      Find (is, diff c c', diff t t', diff e e')
  | Atom a, Atom a' when a=a' -> Atom a
  | Atom (`Message (o,u,v)), Atom (`Message (o',u',v')) when o=o' ->
      Atom (`Message (o, diff u u', diff v v'))
  | ForAll (vs,f), ForAll (vs',f') when vs=vs' -> ForAll (vs, diff f f')
  | Exists (vs,f), Exists (vs',f') when vs=vs' -> Exists (vs, diff f f')
  | And  (f,g), And  (f',g') -> And  (diff f f', diff g g')
  | Or   (f,g), Or   (f',g') -> Or   (diff f f', diff g g')
  | Impl (f,g), Impl (f',g') -> Impl (diff f f', diff g g')
  | Not f, Not f' -> Not (diff f f')
  | True, True -> True
  | False, False -> False
  | t,t' -> diff t t'

let make_bi_term  : type a. a term -> a term -> a term = fun t1 t2 ->
  head_normal_biterm (Diff (t1, t2))

let () =
  let mkvar x s = Var (snd (Vars.make_fresh Vars.empty_env s x)) in
  Checks.add_suite "Head normalization" [
    "Macro, different ts", `Quick, begin fun () ->
      let ts = mkvar "ts" Sorts.Timestamp in
      let ts' = mkvar "ts'" Sorts.Timestamp in
      let m = in_macro in
      let t = Diff (Macro (m,[],ts), Macro (m,[],ts')) in
      let r = head_normal_biterm t in
      assert (r = t)
    end ;
    "Boolean operator", `Quick, begin fun () ->
      let f = mkvar "f" Sorts.Boolean in
      let g = mkvar "g" Sorts.Boolean in
      let f' = mkvar "f'" Sorts.Boolean in
      let g' = mkvar "g'" Sorts.Boolean in
      let t = Diff (And (f,g), And (f',g')) in
        assert (head_normal_biterm t = And (Diff (f,f'), Diff (g,g')))
    end ;
  ] ;
  Checks.add_suite "Projection" [
    "Simple example", `Quick, Symbols.run_restore @@ begin fun () ->
      let a = mkvar "a" Sorts.Message in
      let b = mkvar "b" Sorts.Message in
      let c = mkvar "c" Sorts.Message in
      let def = Symbols.Abstract 2 in
      let _,f =
        Symbols.Function.declare_exact Symbols.empty_table "f" (0,def) in
      let f x = Fun ((f,[]),[x]) in
      let t = Diff (f (Diff(a,b)), c) in
      let r = head_pi_term Left t in
        assert (pi_term  ~projection:Left t = f a) ;
        assert (r = f (Diff (a,b)))
    end ;
  ]
