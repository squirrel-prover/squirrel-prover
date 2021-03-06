open Utils

module L = Location

module Sv = Vars.Sv
module Mv = Vars.Mv

let dbg s = Printer.prt `Ignore s
(* let dbg s = Printer.prt `Dbg s *)

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

let pp_mname_s ppf s =
  let open Fmt in
  (styled `Bold (styled `Magenta Utils.ident)) ppf s

let pp_mname ppf s =
  pp_mname_s ppf (Symbols.to_string s)

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

type index_atom = [ `Index of (ord_eq,Vars.index) _atom]
                    
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
  | Seq _ -> Sorts.Message
  | Var v -> Vars.sort v
  | Pred _ -> Sorts.Timestamp
  | Action _ -> Sorts.Timestamp
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

(*------------------------------------------------------------------*)
exception Uncastable

let cast: type a b. a Sorts.sort -> b term -> a term =
  fun kind t ->
  match kind, sort t with
     | Sorts.Index, Sorts.Index -> t
     | Sorts.Message, Sorts.Message -> t
     | Sorts.Boolean, Sorts.Boolean -> t
     | Sorts.Timestamp, Sorts.Timestamp -> t
     | _ -> raise Uncastable


                
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

(** Init action *)
let init = Action(Symbols.init_action,[])

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
    Fmt.pf ppf "%a ^ %a" pp t1 pp t2
      
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
  Fmt.pf ppf "@[<hv 2>%a(%a)@]"
    pp_mname_s "happens"
    (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt ",@ ") pp) ts
  
and pp_and_happens ppf f =
  let rec collect acc = function
    | And (l, r) -> collect (collect acc l) r
    | Atom (`Happens ts) -> ts :: acc
    | _ -> assert false in

  pp_happens ppf (collect [] f)

let pp_eq_atom ppf at = pp_generic_atom ppf (at :> generic_atom)


(*------------------------------------------------------------------*)
(** Literals. *)

type literal = [`Neg | `Pos] * generic_atom

type eq_literal = [`Pos | `Neg] * eq_atom

type trace_literal = [`Pos | `Neg] * trace_atom

let pp_literal fmt ((pn,at) : literal) =
  match pn with
  | `Pos -> Fmt.pf fmt "%a"    pp_generic_atom at
  | `Neg -> Fmt.pf fmt "??(%a)" pp_generic_atom at

let pp_literals fmt (l : literal list) = 
  let sep fmt () = Fmt.pf fmt " ??? " in
  (Fmt.list ~sep pp_literal) fmt l

let pp_trace_literal fmt (lit : trace_literal) =
  pp_literal fmt (lit :> literal)

let pp_trace_literals fmt (l : trace_literal list) = 
  pp_literals fmt (l :> literal list)

let neg_lit ((pn, at) : literal) : literal = 
  let pn = match pn with
    | `Pos -> `Neg
    | `Neg -> `Pos in
  (pn, at)

let neg_trace_lit ((pn, at) : trace_literal) : trace_literal = 
  let pn = match pn with
    | `Pos -> `Neg
    | `Neg -> `Pos in
  (pn, at)


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
let atom_triv = function
  | `Message   (`Eq,t1,t2) when t1=t2 -> true
  | `Timestamp (`Eq,t1,t2) when t1=t2 -> true
  | `Index     (`Eq,i1,i2) when i1=i2 -> true
  | _ -> false 

let f_triv = function
  | True -> true
  | Atom atom -> atom_triv atom
  | _ -> false 

    
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

(*------------------------------------------------------------------*)

let get_set_vars : 'a term -> Sv.t =
  fun term ->

  let rec termvars : type a. a term -> Sv.t -> Sv.t = fun t vars -> match t with
    | Action (_,indices) -> Sv.add_list vars indices
    | Var tv -> Sv.add (Vars.EVar tv) vars
    | Pred ts -> termvars ts vars
    | Fun ((_,indices), lt) ->
        let vars = Sv.add_list vars indices in
        List.fold_left (fun vars x -> termvars x vars) vars lt

    | Macro ((_,_,indices), l, ts) ->
      let vars = Sv.add_list vars indices in
      termvars ts (termsvars l vars)
    | Seq (a, b) ->
      Sv.diff
        (termvars b vars)
        (Sv.of_list (List.map (fun x -> Vars.EVar x) a))
    | Name (_,indices) -> Sv.add_list vars indices
    | Diff (a, b) -> termvars a (termvars b vars)
    | ITE (a, b, c) -> termvars a (termvars b (termvars c vars))
    | Find (a, b, c, d) ->
      Sv.diff
        (termvars b (termvars c (termvars d vars)))
        (Sv.of_list (List.map (fun x -> Vars.EVar x) a))
    | Atom a -> generic_atom_vars a vars
    | ForAll (a, b) -> Sv.diff (termvars b vars) (Sv.of_list a)
    | Exists (a, b) -> Sv.diff (termvars b vars) (Sv.of_list a)
    | And (a, b) ->  termvars a (termvars b vars)
    | Or (a, b) ->  termvars a (termvars b vars)
    | Not a -> termvars a vars
    | Impl (a, b) ->  termvars a (termvars b vars)
    | True -> vars
    | False -> vars

  and termsvars : type a. a term list -> Sv.t -> Sv.t = fun terms vars ->
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
  
  termvars term Sv.empty

let get_vars t = get_set_vars t |> Sv.elements

let fv t = get_set_vars t

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

let mk_forall l f = 
  if l = [] then f 
  else match f with
    | ForAll (l', f) -> ForAll (l @ l', f)
    | _ -> ForAll (l, f)

let mk_exists l f = 
  if l = [] then f 
  else match f with
    | Exists (l', f) -> Exists (l @ l', f)
    | _ -> Exists (l, f)

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
(** {2 Substitutions} *)

(** given a variable [x] and a subst [s], remove from [s] all
    substitution [v->_]. *)
let filter_subst (var:Vars.evar) (s:subst) =
  let s = 
    List.fold_left (fun acc (ESubst (x, y)) ->
        if not (Sv.mem var (get_set_vars x))
        then (ESubst (x, y))::acc
        else acc
      ) [] s in 

  List.rev s

(** Check if the substitutions only susbtitutes variables *)
let is_var_subst s =
  List.for_all (fun (ESubst (t,_)) -> match t with
      | Var _ -> true
      | _ -> false) s

(** Returns the variables appearing in a substitution LHS. *)
let subst_support s =
  List.fold_left (fun supp (ESubst (t,_)) -> 
    Sv.union supp (get_set_vars t)) Sv.empty s

let rec subst : type a. subst -> a term -> a term = fun s t ->
  if is_var_subst s && 
     Sv.disjoint (subst_support s) (get_set_vars t)
  then t
  else
    let new_term : a term =
      match t with
      | Fun ((fs,is), lt) ->
        Fun ((fs, List.map (subst_var s) is),
             List.map (subst s) lt)
      | Name (ns,is) -> Name (ns, List.map (subst_var s) is)
      | Macro (m, l, ts) ->
        Macro (subst_macro s m, List.map (subst s) l, subst s ts)

      (* Seq in annoying to do *)
      | Seq ([], f) -> Seq ([], subst s f)

      | Seq ([a], f) -> 
        let a, f = subst_binding (Vars.EVar a) s f in
        let a = Vars.ecast a Sorts.Index in
        Seq ([a],f)

      | Seq (a :: vs, f) -> 
        let a, f = subst_binding (Vars.EVar a) s (Seq (vs,f)) in
        let a = Vars.ecast a Sorts.Index in
        let vs, f = match f with
          | Seq (vs, f) -> vs, f
          | _ -> assert false in
        Seq (a :: vs,f)

      | Var m -> Var m
      | Pred ts -> Pred (subst s ts)
      | Action (a,indices) -> Action (a, List.map (subst_var s) indices)
      | Diff (a, b) -> Diff (subst s a, subst s b)
      | ITE (a, b, c) -> ITE (subst s a, subst s b, subst s c)
      | Atom a-> Atom (subst_generic_atom s a)
      | And (a, b) -> And (subst s a, subst s b)
      | Or (a, b) -> Or (subst s a, subst s b)
      | Not a -> Not (subst s a)
      | Impl (a, b) -> Impl (subst s a, subst s b)
      | True -> True
      | False -> False

      | ForAll ([], f) -> subst s f

      | ForAll (a :: vs, f) ->
        let a, f = subst_binding a s (ForAll (vs,f)) in
        mk_forall [a] f

      | Exists ([], f) -> subst s f

      | Exists (a :: vs, f) ->
        let a, f = subst_binding a s (Exists (vs,f)) in
        mk_exists [a] f

      | Find ([], b, c, d) -> Find ([], subst s b, subst s c, subst s d) 

      | Find (v :: vs, b, c, d) -> 
        (* used because [v :: vs] are not bound in [d]  *)
        let dummy = Fun (f_zero,[]) in

        let v, f = subst_binding (Vars.EVar v) s (Find (vs, b, c, dummy)) in
        let v = Vars.ecast v Sorts.Index in
        match f with
        | Find (vs, b, c, _) -> Find (v :: vs, b, c, subst s d) 
        | _ -> assert false
    in 
    assoc s new_term

and subst_binding 
  : type a. Vars.evar -> esubst list -> a term -> Vars.evar * a term =
  fun var s f ->
  (* clear [v] entries in [s] *)
  let s = filter_subst var s in

  let right_fv = 
    List.fold_left (fun acc (ESubst (x, y)) -> 
        Sv.union acc (get_set_vars y)
      ) Sv.empty s in

  let all_vars = 
    List.fold_left (fun acc (ESubst (x, y)) -> 
        Sv.union acc (get_set_vars x)
      ) right_fv s in

  let env = ref (Vars.of_list (Sv.elements all_vars)) in

  (* if [v] is appears in the RHS of [s], refresh [v] carefully *)
  let var, s = 
    if Sv.mem var right_fv 
    then 
      match var with 
      | Vars.EVar v ->
        let new_v = Vars.make_fresh_from_and_update env v in
        let s = (ESubst (Var v,Var new_v)) :: s in
        ( Vars.EVar new_v, s)
    else ( var, s ) in
  
  var, subst s f

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
type eterm = ETerm : 'a term -> eterm

(** [app func t] applies [func] to [t]. [func] must preserve types. *)
let app : type a. (eterm -> eterm) -> a term -> a term = 
  fun func x ->
  let ETerm x0 = func (ETerm x) in
  cast (sort x) x0
  
let atom_map (func : eterm -> eterm) (at : generic_atom) : generic_atom =
  let func : type c. c term -> c term = fun x -> app func x in

  match at with
  | `Message (o,t1,t2) -> 
    let t1 = func t1
    and t2 = func t2 in
    `Message (o, t1, t2)

  | `Timestamp (o,t1,t2) ->
    let t1 = func t1
    and t2 = func t2 in
    `Timestamp (o, t1, t2)
      
  | `Index (o,t1,t2) ->     
    let t1 = match func (Var t1) with
      | Var t1 -> t1
      | _ -> assert false
    and t2 = match func (Var t2) with
      | Var t2 -> t2
      | _ -> assert false
    in
    `Index (o, t1, t2)

  | `Happens t -> `Happens (func t)

(** Does not recurse. 
    Applies to arguments of index atoms (see atom_map). *)
let tmap : type a. (eterm -> eterm) -> a term -> a term = 
  fun func0 t -> 
  let func : type c. c term -> c term = fun x -> app func0 x in

  match t with
  | True     -> t  
  | False    -> t  
  | Action _ -> t
  | Name _   -> t
  | Var _    -> t
      
  | Fun (f,terms)     -> Fun (f, List.map func terms)
  | Macro (m, l, ts)  -> Macro (m, List.map func l, func ts) 
  | Seq (vs, b)       -> Seq (vs, func b)      
  | Pred ts           -> Pred (func ts)                 

  | Diff (bl, br)     -> 
    let bl = func bl in
    let br = func br in
    Diff (bl, br)      

  | ITE (b, c, d) -> 
    let b = func b 
    and c = func c
    and d = func d in
    ITE (b, c, d)        

  | Find (b, c, d, e) -> 
    let c = func c 
    and d = func d 
    and e = func e in
    Find (b, c, d, e)
        
  | ForAll (vs, b)    -> ForAll (vs, func b)      
  | Exists (vs, b)    -> Exists (vs, func b)

  | And (a,b) -> 
    let a = func a 
    and b = func b in
    And (a, b)

  | Or (a,b) -> 
    let a = func a 
    and b = func b in
    Or (a, b)

  | Impl (a,b) -> 
    let a = func a 
    and b = func b in
    Impl (a, b)

  | Not b -> Not (func b)      
  | Atom at -> Atom (atom_map func0 at)

let titer (f : eterm -> unit) (t : 'a term) : unit = 
  let g e = f e; e in
  ignore (tmap g t)

let tfold : type a. (eterm -> 'b -> 'b) -> a term -> 'b -> 'b = 
  fun f t v -> 
  let vref : 'b ref = ref v in
  let fi e = vref := (f e !vref) in  
  titer fi t;
  !vref

(*------------------------------------------------------------------*)
(** {2 Matching and rewriting} *)

module Match = struct 
  (** Variable assignment (types must be compatible). *)
  type mv = eterm Mv.t

  let to_subst (mv : mv) : subst =
    Mv.fold (fun v t subst -> 
        match v, t with
        | Vars.EVar v, ETerm t -> 
          ESubst (Var v, cast (Vars.sort v) t) :: subst
      ) mv [] 

  (** A pattern is a term [t] and a subset of [t]'s free variables that must 
      be matched.  *)
  type 'a pat = { p_term : 'a term; p_vars : Sv.t }

  let pp_pat fmt p =
    Fmt.pf fmt "@[<hov 0>{term = @[%a@];@ vars = @[%a@]}@]"
      pp p.p_term 
      (Fmt.list ~sep:Fmt.sp Vars.pp_e) (Sv.elements p.p_vars)

  (** [try_match t p] tries to match [p] into [t]. If it succeeds, it 
      returns a map instantiating the variables [p.p_vars] as substerms 
      of [t]. *)
  let try_match : type a b. a term -> b pat -> mv option = 
    fun t p -> 
    let exception NoMatch in
    dbg "try_match: %a with %a" pp t pp_pat p;

    
    (* Invariant: [mv] supports in included in [p.p_vars]. *)
    let rec tmatch : type a b. a term -> b term -> mv -> mv =
      fun t pat mv -> match t, pat with
        | _, Var v' -> 
          begin
            match cast (Vars.sort v') t with
            | exception Uncastable -> raise NoMatch
            | t -> vmatch t v' mv
          end

        | Fun (symb, terms), Fun (symb', terms') -> 
          let mv = smatch symb symb' mv in
          tmatch_l terms terms' mv

        | Name symb, Name symb' -> 
          smatch symb symb' mv

        | Macro ((s, sort, is), terms, ts), 
          Macro ((s', sort', is'), terms', ts') -> 
          if not (Sorts.equal sort sort') then raise NoMatch;

          let mv = smatch (s,is) (s',is') mv in
          tmatch ts ts' (tmatch_l terms terms' mv)

        | Seq _, _ -> raise NoMatch

        | Pred ts, Pred ts' -> tmatch ts ts' mv

        | Action (s,is), Action (s',is') -> smatch (s,is) (s',is') mv

        | Diff (a,b), Diff (a', b') ->
          tmatch_l [a;b] [a';b'] mv (* TODO: check this *)

        | ITE (b,t1,t2), ITE (b',t1',t2') ->
          tmatch_l [t1;t2] [t1';t2'] (tmatch b b' mv)

        | Find _, _ -> raise NoMatch

        | Atom at, Atom at' -> atmatch at at' mv

        | ForAll _, _ 
        | Exists _, _ -> raise NoMatch

        | And (a,b), And (a', b') 
        | Or (a,b), Or (a', b') 
        | Impl (a,b), Impl (a', b') ->
          tmatch_l [a;b] [a';b'] mv

        | Not a, Not a' -> tmatch a a' mv

        | True, True -> mv
        | False, False -> mv

        | _, _ -> raise NoMatch

    and tmatch_l : type a b. a term list -> b term list -> mv -> mv =
      fun tl patl mv -> 
        List.fold_left2 (fun mv t pat -> tmatch t pat mv) mv tl patl

    and smatch : type a. 
      (a Symbols.t * Vars.index list) -> 
      (a Symbols.t * Vars.index list) -> 
      mv -> mv = 
      fun (fn, is) (fn', is') mv ->

        if fn <> fn' then raise NoMatch;

        List.fold_left2 (fun mv i i' -> vmatch (Var i) i' mv) mv is is'

    (* Match a variable of the pattern with a term. *)
    and vmatch : type a. a term -> a Vars.var -> mv -> mv = fun t v mv ->
      let ev = Vars.EVar v in
      
      if not (Sv.mem ev p.p_vars) 
      then if t = Var v then mv else raise NoMatch (* [v] not in the pattern *)

      else (* [v] in the pattern *)
        match Mv.find ev mv with
        (* If this is the first time we see the variable, store the subterm. *)
        | exception Not_found -> Mv.add ev (ETerm t) mv

        (* If we already saw the variable, check that the subterms are
           identical. *)
        | ETerm t' -> match cast (sort t) t' with
          | exception Uncastable -> raise NoMatch
          (* TODO: alpha-equivalent *)
          | t' -> if t <> t' then raise NoMatch else mv

    and atmatch (at : generic_atom) (at' : generic_atom) mv =
      match at, at' with
      | `Message (ord, t1, t2), `Message (ord', t1', t2') -> 
        if ord <> ord' then raise NoMatch;
        tmatch_l [t1;t2] [t1';t2'] mv

      | `Timestamp (ord, t1, t2), `Timestamp (ord', t1', t2') -> 
        if ord <> ord' then raise NoMatch;
        tmatch_l [t1;t2] [t1';t2'] mv

      | `Index (ord, t1, t2), `Index (ord', t1', t2') -> 
        if ord <> ord' then raise NoMatch;
        tmatch_l [Var t1; Var t2] [Var t1'; Var t2'] mv

      | `Happens ts, `Happens ts' -> tmatch ts ts' mv

      | _, _ -> raise NoMatch
    in

    try Some (tmatch t p.p_term Mv.empty) with
    | NoMatch -> dbg "match failed"; None


  (** Occurrence matched *)
  type 'a match_occ = { occ : 'a term;
                        mv  : mv; }
                        
  (** [find_map t pat func] behaves has [find], but also computes the term 
      obtained from [t] by replacing a *single* occurence of [t'] by 
      [func t' ??]. *)
  let find_map :
    type a b. a term -> b pat -> (b term -> mv -> b term) -> 
    (b match_occ * a term) option
    = fun t p func ->
      let found = ref None in
      let s_p = sort p.p_term in
      
      dbg "find_map: %a with %a" pp t pp_pat p;

      let rec find : type a. a term -> a term = fun t ->
        dbg "find in: %a" pp t;

        if (!found) <> None then (dbg "already found"; t) (* we already found a match *)

        (* no match yet, check if head matches *)
        else 
          match try_match t p with
          (* head does not match, recurse  *)
          | None -> 
            dbg "head no match";
            tmap (fun (ETerm t) -> ETerm (find t)) t

          | Some mv -> (* head matches *)
            dbg "head match";
            found := Some ({ occ = cast s_p t; mv = mv; }); 
            let t' = func (cast s_p t) mv in
            cast (sort t) t'    (* cast needed *)
      in
      
      let t = find t in
      match !found with
      | None -> None
      | Some occ -> Some (occ,t)

  (** [find t pat] looks for an occurence [t'] of [pat] in [t],
      where [t'] is a subterm of [t] and [t] and [t'] are unifiable by [??].
      It returns the occurrence matched [{occ = t'; mv = ??}]. *)
  let find : type a b. a term -> b pat -> b match_occ option = 
    fun t p -> 
    omap fst (find_map t p (fun t' _ -> t'))
end

(*------------------------------------------------------------------*)
(** {2 Simplification} *)

let not_ord_eq o = match o with
  | `Eq -> `Neq
  | `Neq -> `Eq

let not_ord_eq (o,l,r) = (not_ord_eq o, l, r)

(*------------------------------------------------------------------*)
let not_message_atom (at : message_atom) = match at with
  | `Message t          -> `Message (not_ord_eq t)

let not_index_atom (at : index_atom) = match at with
  | `Index t            -> `Index (not_ord_eq t)

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
(** {2 Projection} *)

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
(** {2 Destructors} *)

let rec destr_exists = function
  | Exists (vs, f) -> 
    begin
      match destr_exists f with
      | Some (vs', f) -> Some (vs @ vs', f)
      | None -> Some (vs, f)
    end
  | _ -> None

let rec decompose_exists = function
  | Exists (vs, f) -> 
    let vs', f0 = decompose_exists f in
    vs @ vs', f0
  | _ as f -> [], f

let rec destr_forall = function
  | ForAll (vs, f) -> 
    begin
      match destr_forall f with
      | Some (vs', f) -> Some (vs @ vs', f)
      | None -> Some (vs, f)
    end
  | _ -> None

let rec decompose_forall = function
  | ForAll (vs, f) -> 
    let vs', f0 = decompose_forall f in
    vs @ vs', f0
  | _ as f -> [], f

let rec destr_or = function
  | Or (f, g) -> Some (f,g) 
  | _ -> None

let rec destr_ors l f = match l, f with
  | _ when l < 0 -> assert false
  | 1, _ -> Some [f]
  | _, Or (f, g) -> omap (fun l -> l @ [g]) (destr_ors (l-1) f)
  | _ -> None

let rec decompose_ors f = match f with
  | Or (f, g) -> decompose_ors f @ decompose_ors g
  | _ -> [f]

let rec destr_and = function
  | And (f, g) -> Some (f,g) 
  | _ -> None

let rec destr_ands l f = match l, f with
  | _ when l < 0 -> assert false
  | 1, _ -> Some [f]
  | _, And (f, g) -> omap (fun l -> l @ [g]) (destr_ands (l-1) f)
  | _ -> None

let rec decompose_ands f = match f with
  | And (f, g) -> decompose_ands f @ decompose_ands g
  | _ -> [f]

let rec destr_impl = function
  | Impl (f, g) -> Some (f,g) 
  | _ -> None

let rec destr_impls l f = match l, f with
  | _ when l < 0 -> assert false
  | 1, _ -> Some [f]
  | _, Impl (f, g) -> omap (fun l -> l @ [g]) (destr_impls (l-1) f)
  | _ -> None

let rec decompose_impls f = match f with
  | Impl (f, g) -> decompose_impls f @ decompose_impls g
  | _ -> [f]

let destr_pair : type a. a term -> (a term * a term) option = function
  | Fun (f_pair, terms) ->
    let t1, t2 = as_seq2 terms in
    Some (t1, t2)

  | _ -> None

let destr_var : type a. a term -> a Vars.var option = function
  | Var v -> Some v
  | _ -> None

type eatom = 
  | EOrd : ord * 'a term * 'a term -> eatom
  | EHappens : timestamp -> eatom
      
let destr_atom (at : generic_atom) : eatom = 
  match at with
  | `Message (ord, a, b)   -> EOrd ((ord :> ord), a, b)
  | `Timestamp (ord, a, b) -> EOrd (ord, a, b)
  | `Index (ord, a, b)     -> EOrd ((ord :> ord), Var a, Var b)
  | `Happens t             -> EHappens t

let as_ord_eq (ord : ord) : ord_eq = match ord with
  | `Eq  -> `Eq
  | `Neq -> `Neq
  | _ -> assert false

let of_eatom (eat : eatom) : generic_atom = match eat with
  | EHappens t -> `Happens t
  | EOrd (ord, t1, t2) ->
    match sort t1 with
    | Sorts.Message   -> `Message   (as_ord_eq ord, t1, t2)
    | Sorts.Timestamp -> `Timestamp (ord, t1, t2)
    | Sorts.Index     ->
      let i1, i2 = oget (destr_var t1), oget (destr_var t2) in
      `Index (as_ord_eq ord, i1, i2)

    | Sorts.Boolean   -> assert false

(*------------------------------------------------------------------*)
(** {2 Sets and Maps } *)

module T = struct
  type t = eterm
  let compare = Stdlib.compare
end

module Mt = Map.Make (T)
module St = Set.Make (T)

(*------------------------------------------------------------------*)
(** {2 Tests} *)

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
        Symbols.Function.declare_exact 
          Symbols.builtins_table (L.mk_loc L._dummy "f") (0,def) in
      let f x = Fun ((f,[]),[x]) in
      let t = Diff (f (Diff(a,b)), c) in
      let r = head_pi_term PLeft t in
        assert (pi_term  ~projection:PLeft t = f a) ;
        assert (r = f (Diff (a,b)))
    end ;
  ]
