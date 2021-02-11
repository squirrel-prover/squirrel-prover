module L = Location

(*------------------------------------------------------------------*)
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

(*------------------------------------------------------------------*)
(** Atoms and terms *)

type ord = [ `Eq | `Neq | `Leq | `Geq | `Lt | `Gt ]
type ord_eq = [ `Eq | `Neq ]

type ('a,'b) _atom = 'a * 'b * 'b
             
type generic_atom = [
  | `Message   of (ord_eq, Sorts.message term)   _atom
  | `Timestamp of (ord,    Sorts.timestamp term) _atom
  | `Index     of (ord_eq, Vars.index)           _atom
  | `Happens   of Sorts.timestamp term
]

and _ term =
  | Fun    : fsymb *  Sorts.message term list -> Sorts.message term
  | Name   : nsymb -> Sorts.message term
  | Macro  :
      'a msymb * Sorts.message term list * Sorts.timestamp term ->
      'a term
  | Seq    : Vars.index list * Sorts.message term -> Sorts.message term
  | Pred   : Sorts.timestamp term -> Sorts.timestamp term        
  | Action :
      Symbols.action Symbols.t * Vars.index list ->
      Sorts.timestamp term
  | Init   : Sorts.timestamp term
  | Var    : 'a Vars.var -> 'a term

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
  | And    : Sorts.boolean term * Sorts.boolean term -> Sorts.boolean term
  | Or     : Sorts.boolean term * Sorts.boolean term -> Sorts.boolean term
  | Not    : Sorts.boolean term -> Sorts.boolean term
  | Impl   : Sorts.boolean term * Sorts.boolean term -> Sorts.boolean term
  | True   : Sorts.boolean term
  | False  : Sorts.boolean term

type 'a t = 'a term

(*------------------------------------------------------------------*)
type message = Sorts.message term
type timestamp = Sorts.timestamp term
type formula = Sorts.boolean term

(*------------------------------------------------------------------*)
(** Subset of all atoms (the subsets are not disjoint). *)
    
type message_atom = [ `Message of (ord_eq,Sorts.message term) _atom]
                    
type trace_atom = [
  | `Timestamp of (ord,timestamp) _atom
  | `Index     of (ord_eq,Vars.index) _atom
  | `Happens   of Sorts.timestamp term
]

type trace_eq_atom = [
  | `Timestamp of (ord_eq, timestamp) _atom
  | `Index     of (ord_eq, Vars.index) _atom
]

(* Subsets of atoms that are equalities *)
type eq_atom = [
  | `Message   of (ord_eq, message) _atom
  | `Timestamp of (ord_eq, timestamp) _atom
  | `Index     of (ord_eq, Vars.index) _atom
]

(*------------------------------------------------------------------*)
let rec sort : type a. a term -> a Sorts.t =
  function
  | Fun _               -> Sorts.Message
  | Name _              -> Sorts.Message
  | Macro ((_,s,_),_,_) -> s
  | Seq _               -> Sorts.Message
  | Var v               -> Vars.sort v
  | Pred _              -> Sorts.Timestamp
  | Action _            -> Sorts.Timestamp
  | Init                -> Sorts.Timestamp
  | Diff (a, b)         -> sort a
  | ITE (a, b, c)       -> Sorts.Message
  | Find (a, b, c, d)   -> Sorts.Message
  | Atom _              -> Sorts.Boolean
  | ForAll _            -> Sorts.Boolean
  | Exists _            -> Sorts.Boolean
  | And _               -> Sorts.Boolean
  | Or _                -> Sorts.Boolean
  | Not _               -> Sorts.Boolean
  | Impl _              -> Sorts.Boolean
  | True                -> Sorts.Boolean
  | False               -> Sorts.Boolean

(*------------------------------------------------------------------*)
let disjunction_to_literals f =
  let exception Not_a_disjunction in

  let rec aux = function
  | False -> []
  | Atom at -> [`Pos, at]
  | Not (Atom at) -> [`Neg, at]
  | Or (a, b) -> aux a @ aux b
  | _ -> raise Not_a_disjunction in

  try Some (aux f) with Not_a_disjunction -> None

(*------------------------------------------------------------------*)
(** Builtins *)

let mk f : fsymb = (f,[])

let f_diff = mk Symbols.fs_diff

(** Boolean function symbols, where booleans are typed as messages.
  * The true/false constants are used in message_of_formula,
  * and other symbols are used in an untyped way in Completion
  * (in some currently unused code). *)

let eboolean,emessage = Sorts.eboolean,Sorts.emessage

(** Boolean connectives *)

let f_false  = mk Symbols.fs_false
let f_true   = mk Symbols.fs_true
let f_and    = mk Symbols.fs_and
let f_or     = mk Symbols.fs_or
let f_not    = mk Symbols.fs_not
let f_ite    = mk Symbols.fs_ite

(** Fail *)

let f_fail   = mk Symbols.fs_fail

(** Xor and its unit *)

let f_xor    = mk Symbols.fs_xor
let f_zero   = mk Symbols.fs_zero

(** Successor over natural numbers *)

let f_succ   = mk Symbols.fs_succ

(** Pairing *)

let f_pair   = mk Symbols.fs_pair
let f_fst    = mk Symbols.fs_fst
let f_snd    = mk Symbols.fs_snd

(** Exp **)

let f_exp    = mk Symbols.fs_exp
let f_g      = mk Symbols.fs_g

(** Empty *)

let empty    = Fun (mk Symbols.fs_empty, [])

(** Length *)

let f_len    = mk Symbols.fs_len
let f_zeroes = mk Symbols.fs_zeroes

(*------------------------------------------------------------------*)
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

let rec is_and_happens = function
  | And (l, r) -> is_and_happens l && is_and_happens r
  | Atom (`Happens _) -> true
  | _ -> false

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

  | And _ as f when is_and_happens f ->
    pp_and_happens ppf f
                                     
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

  | `Happens a -> pp_happens ppf [a]

and pp_generic_atom ppf = function                   
  | #message_atom as a -> pp_message_atom ppf a
                            
  | #trace_atom as a -> pp_trace_atom ppf a

and pp_happens ppf (ts : timestamp list) =
  Fmt.pf ppf "@[<hv 2>happens(%a)@]"
    (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt ",@ ") pp) ts
  
and pp_and_happens ppf f =
  let rec collect acc = function
    | And (l, r) -> collect (collect acc l) r
    | Atom (`Happens ts) -> [ts]
    | _ -> assert false in

  pp_happens ppf (collect [] f)
    
(*------------------------------------------------------------------*)
(** Declare input and output macros.
  * We assume that they are the only symbols bound to Input/Output. *)
let in_macro    = (Symbols.inp,   Sorts.Message, [])
let out_macro   = (Symbols.out,   Sorts.Message, [])
let frame_macro = (Symbols.frame, Sorts.Message, [])

let cond_macro  = (Symbols.cond, Sorts.Boolean, [])
let exec_macro  = (Symbols.exec, Sorts.Boolean, [])

let rec pts : type a. timestamp list -> a term -> timestamp list = fun acc -> function
  | Fun (_, lt) -> List.fold_left pts acc lt
  | Macro (s, l, ts) ->
     if Obj.magic s = in_macro then (Pred ts) :: acc else
       List.fold_left pts (ts :: acc) l
  | Name _ -> acc
  | Var _ -> []
  | ITE (f,t,e) -> List.fold_left pts (pts acc f) [t;e]
  | _ -> failwith "Not implemented"

let precise_ts t = pts [] t |> List.sort_uniq Stdlib.compare

(*------------------------------------------------------------------*)
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
      termvars ts (termsvars l vars)
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

  and termsvars : type a. a term list -> S.t -> S.t = fun terms vars ->
    List.fold_left (fun vars x -> termvars x vars) vars terms
    
  and message_atom_vars (`Message (ord, a1, a2)) vars =
   termvars a1 (termvars a2 vars)

  and trace_atom_vars at vars = match at with
    | `Timestamp (ord, ts, ts') ->
      termvars ts (termvars ts' vars)
    | `Index (ord, i, i') ->
      termvars (Var i) (termvars (Var i') vars)
    | `Happens ts -> termvars ts vars
                       
  and generic_atom_vars t vars = match t with
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
        if S.is_empty (S.inter (S.of_list vars) (get_set_vars x))
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
    let env = ref (Vars.of_list (S.elements all_vars)) in
    let v, f = List.fold_left
     (fun  (nvars,f) (Vars.EVar v) ->
            if S.mem (Vars.EVar v) right_vars then
              let new_v = Vars.make_fresh_from_and_update env v in
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
  | `Happens a -> `Happens (subst s a)
                            
  | `Timestamp (ord, ts, ts') ->
    `Timestamp (ord, subst s ts, subst s ts')
      
  | `Index (ord, i, i') ->
    `Index(ord, subst_var s i,subst_var s i')
      
and subst_generic_atom s = function
  | #message_atom as a -> (subst_message_atom s a :> generic_atom)
  | #trace_atom   as a -> (subst_trace_atom s a :> generic_atom)

let subst_macros_ts table l ts t =
  let rec subst_term : type a. a term -> a term = fun t -> match t with
    | Macro ((symb,s,ind), terms, ts') ->
      let terms' = List.map subst_term terms in
      begin match Symbols.Macro.get_all symb table with
      | Symbols.State _, _ ->
        if (List.mem (Symbols.to_string symb) l && ts=ts')
        then Macro((symb,s,ind), terms', ts')
        else Macro((symb,s,ind), terms', Pred(ts'))
      | _ -> Macro((symb,s,ind), terms', ts')
      end
    | Fun (f,terms) -> Fun (f, List.map subst_term terms)
    | Seq (a, b) -> Seq (a, subst_term b)
    | Diff (a, b) -> Diff (subst_term a, subst_term b)
    | ITE (a, b, c) -> ITE (subst_term a, subst_term b, subst_term c)
    | Find (vs, b, t, e) -> Find (vs, subst_term b, subst_term t, subst_term e)
    | ForAll (vs, b) -> ForAll (vs, subst_term b)
    | Exists (vs, b) -> Exists (vs, subst_term b)
    | And (a, b) -> And (subst_term a, subst_term b)
    | Or (a, b) -> Or (subst_term a, subst_term b)
    | Not a -> Not (subst_term a)
    | Impl (a, b) -> Impl (subst_term a, subst_term b)
    | Atom a -> Atom (subst_generic_atom a)
    | _ -> t
  and subst_message_atom (`Message (ord, a1, a2)) =
    `Message (ord, subst_term a1, subst_term a2)
  and subst_generic_atom a = match a with
    | #message_atom as a -> (subst_message_atom a :> generic_atom)
    | _ -> a
  in
  subst_term t


(*------------------------------------------------------------------*)
(** Smart constructors for boolean terms. *)

let mk_not t1 = match t1 with
  | Not t -> t
  | t -> Not t

let mk_and t1 t2 = match t1,t2 with
  | True, t | t, True -> t
  | t1,t2 -> And (t1,t2)

let mk_ands ts = List.fold_left mk_and True ts

let mk_or t1 t2 = match t1,t2 with
  | False, t | t, False -> t
  | t1,t2 -> Or (t1,t2)

let mk_ors ts = List.fold_left mk_or False ts

let mk_impl t1 t2 = match t1,t2 with
  | False, _ -> True
  | True, t -> t
  | t1,t2 -> Impl (t1,t2)

let mk_impls ts t =
  List.fold_left (fun tres t0 -> mk_impl t0 tres) t ts

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
    (List.map2 (fun i j ->
         if i = j then True else Atom (`Index (`Eq, i, j))
       ) vect_i vect_j)


(*------------------------------------------------------------------*)
(** Simplification *)

let not_ord_eq o = match o with
  | `Eq -> `Neq
  | `Neq -> `Eq

let not_ord_eq (o,l,r) = (not_ord_eq o, l, r)

(*------------------------------------------------------------------*)
let not_message_atom (at : message_atom) = match at with
  | `Message t          -> `Message (not_ord_eq t)

let not_trace_eq_atom (at : trace_eq_atom) : trace_eq_atom = match at with
  | `Timestamp (o,t,t') -> `Timestamp (not_ord_eq (o,t,t'))
  | `Index (o,i,i')     -> `Index     (not_ord_eq (o,i,i'))

let not_eq_atom (at : eq_atom) : eq_atom = match at with
  | `Timestamp (o,t,t') -> `Timestamp (not_ord_eq (o,t,t'))
  | `Index (o,i,i')     -> `Index     (not_ord_eq (o,i,i'))
  | `Message t          -> `Message   (not_ord_eq t)

let rec not_simpl = function
    | Exists (vs, f) -> ForAll(vs, not_simpl f)
    | ForAll (vs, f) -> Exists(vs, not_simpl f)
    | And (a, b)     -> Or (not_simpl a, not_simpl b)
    | Or (a, b)      -> And (not_simpl a, not_simpl b)
    | Impl (a, b)    -> And(a, not_simpl b)
    | True           -> False
    | False          -> True
    | Not f          -> f
    | Atom atom ->
      begin
        match atom with
        | (`Message _                 as at)
        | (`Index _                   as at)
        | (`Timestamp (#ord_eq, _, _) as at) ->
          Atom (not_eq_atom at :> generic_atom)

        | `Timestamp _ | `Happens _  -> Not (Atom atom)
      end          
    | m -> Not m


(*------------------------------------------------------------------*)
(** Projection *)

type projection = PLeft | PRight | PNone

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
      | PLeft -> pi_term s a
      | PRight -> pi_term s b
      | PNone -> Diff (a, b)
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
   | `Message  (o,t1,t2)      -> `Message (o, pi_term s t1, pi_term s t2)
   | `Timestamp (o, ts1, ts2) -> `Timestamp (o, pi_term s ts1, pi_term s ts2)
   | `Index (o, i1, i2) as r  -> r
   | `Happens t               -> `Happens (pi_term s t)

  in pi_term projection term

let rec head_pi_term : type a. projection -> a term -> a term =
  fun s t ->
  match t,s with
  | Diff (t,_), PLeft
  | Diff (_,t), PRight -> head_pi_term s t
  | _ -> t

let diff a b =
  let a = match a with Diff (a,_) | a -> a in
  let b = match b with Diff (_,b) | b -> b in
  if a = b then a else Diff (a,b)

let head_normal_biterm : type a. a term -> a term = fun t ->
  match head_pi_term PLeft t, head_pi_term PRight t with
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


(*------------------------------------------------------------------*)
(** Tests *)

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
    "Simple example", `Quick, begin fun () ->
      let a = mkvar "a" Sorts.Message in
      let b = mkvar "b" Sorts.Message in
      let c = mkvar "c" Sorts.Message in
      let def = Symbols.Abstract 2 in
      let table,f =
        Symbols.Function.declare_exact Symbols.builtins_table "f" (0,def) in
      let f x = Fun ((f,[]),[x]) in
      let t = Diff (f (Diff(a,b)), c) in
      let r = head_pi_term PLeft t in
        assert (pi_term  ~projection:PLeft t = f a) ;
        assert (r = f (Diff (a,b)))
    end ;
  ]
