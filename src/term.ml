open Utils

module L = Location

module Sv = Vars.Sv
module Mv = Vars.Mv

let dbg s = Printer.prt `Ignore s
(* let dbg s = Printer.prt `Dbg s *)

(*------------------------------------------------------------------*)
(** {2 Symbols} *)

(** Ocaml type of a typed index symbol.
    Invariant: [s_typ] do not contain tvar or univars *)
type ('a,'b) isymb = { 
  s_symb    : 'a;
  s_indices : Vars.index list;
  s_typ     : 'b; 
}

let mk_isymb s t is = 
  let () = match t with
    | Type.TVar _ | Type.TUnivar _ -> assert false;
    | _ -> () 
  in

  { s_symb    = s; 
    s_typ     = t;
    s_indices = is; } 


type name = Symbols.name Symbols.t
type nsymb = (name, Type.tmessage) isymb
                              
type fname = Symbols.fname Symbols.t
type fsymb = fname * Vars.index list (* TODO: use isymb *)

type mname = Symbols.macro Symbols.t
type msymb = (mname, Type.tmessage) isymb

type state = msymb

(*------------------------------------------------------------------*)
let pp_name ppf s = (Utils.kw `Yellow) ppf (Symbols.to_string s)

let pp_nsymb ppf (ns : nsymb) =
  if ns.s_indices <> [] 
  then Fmt.pf ppf "%a(%a)" pp_name ns.s_symb Vars.pp_list ns.s_indices
  else Fmt.pf ppf "%a" pp_name ns.s_symb

let pp_fname ppf s = (Utils.kw `Bold) ppf (Symbols.to_string s)

let pp_fsymb ppf (fn,is) = match is with
  | [] -> Fmt.pf ppf "%a" pp_fname fn
  | _ -> Fmt.pf ppf "%a(%a)" pp_fname fn Vars.pp_list is

let pp_mname_s ppf s =
  let open Fmt in
  (styled `Bold (styled `Magenta Utils.ident)) ppf s

let pp_mname ppf s =
  pp_mname_s ppf (Symbols.to_string s)

let pp_msymb ppf (ms : msymb) =
  Fmt.pf ppf "%a%a"
    pp_mname ms.s_symb
    (Utils.pp_ne_list "(%a)" Vars.pp_list) ms.s_indices

(*------------------------------------------------------------------*)
(** {2 Atoms and terms} *)

type ord    = [ `Eq | `Neq | `Leq | `Geq | `Lt | `Gt ]
type ord_eq = [ `Eq | `Neq ]

type ('a,'b) _atom = 'a * 'b * 'b
             
type generic_atom = [
  | `Message   of (ord_eq, Type.message term)   _atom
  | `Timestamp of (ord,    Type.timestamp term) _atom
  | `Index     of (ord_eq, Vars.index)          _atom
  | `Happens   of Type.timestamp term
]

and _ term =
  | Fun    : fsymb * Type.ftype * Type.message term list -> Type.message term
  | Name   : nsymb -> Type.message term
  | Macro  :
      msymb * Type.message term list * Type.timestamp term ->
      Type.message term

  | Seq    : Vars.evar list * Type.message term -> Type.message term
  | Pred   : Type.timestamp term -> Type.timestamp term        
  | Action :
      Symbols.action Symbols.t * Vars.index list ->
      Type.timestamp term
  | Var    : 'a Vars.var -> 'a term

  | Diff : 'a term * 'a term -> 'a term

  | Find :
      Vars.index list * Type.message term *
      Type.message term * Type.message term ->
      Type.message term

  | Atom : generic_atom -> Type.message term

  | ForAll : Vars.evar list * Type.message term -> Type.message term
  | Exists : Vars.evar list * Type.message term -> Type.message term

type 'a t = 'a term

type eterm = ETerm : 'a term -> eterm

(*------------------------------------------------------------------*)
type message  = Type.message term
type messages = message list

type timestamp  = Type.timestamp term
type timestamps = timestamp list

(*------------------------------------------------------------------*)
let hash_ord : ord -> int = function
  | `Eq -> 1
  | `Neq -> 2
  | `Leq -> 3
  | `Geq -> 4
  | `Lt -> 5
  | `Gt -> 6

let rec hash : type a. a term -> int = function
  | Name n -> hcombine 0 (hash_isymb n)
      
  | Fun ((f, is),_,terms) -> 
    let h = Symbols.hash f in
    let h = hcombine_list Vars.hash h is in
    hcombine 1 (hash_l terms h)

  | Macro (m, l, ts)  -> 
    let h = hcombine_list hash (hash_isymb m) l in
    hcombine 2 (hcombine h (hash ts))

  | Seq (vars, b) -> 
    let h = hcombine_list Vars.ehash (hash b) vars in
    hcombine 3 h

  | Pred ts -> hcombine 4 (hash ts)

  | Diff (bl, br) -> hcombine 5 (hash_l [bl; br] 3)

  | Find (b, c, d, e) -> 
    let h = hcombine_list Vars.hash 6 b in
    hash_l [c;d;e] h
        
  | ForAll (vs, b) -> 
    let h = hcombine_list Vars.ehash (hash b) vs in
    hcombine 7 h

  | Exists (vs, b) -> 
    let h = hcombine_list Vars.ehash (hash b) vs in
    hcombine 8 h

  | Atom at -> hcombine 9 (hash_atom at)

  | Var v -> hcombine 10 (Vars.hash v)

  | Action (s, is) -> 
    let h = hcombine_list Vars.hash (Symbols.hash s) is in
    hcombine 11 h

and hash_l : type a. a term list -> int -> int = fun l h ->
    hcombine_list hash h l

and hash_atom : generic_atom -> int = function
  | `Message (eq, t1, t2) -> 
    hcombine 12 (hash_l [t1;t2] (hash_ord (eq :> ord)))
  | `Timestamp (eq, t1, t2) -> 
    hcombine 13 (hash_l [t1;t2] (hash_ord eq))
  | `Index (eq, t1, t2) -> 
    hcombine 14 (hcombine_list Vars.hash (hash_ord (eq :> ord)) [t1;t2])
  | `Happens t ->
    hcombine 15 (hash t)

(* ignore the type *)      
and hash_isymb : type a. (a Symbols.t, Type.tmessage) isymb -> int = 
  fun symb ->
  let h = Symbols.hash symb.s_symb in
  hcombine_list Vars.hash h symb.s_indices


(*------------------------------------------------------------------*)
(** Subset of all atoms (the subsets are not disjoint). *)
    
type message_atom = [ `Message of (ord_eq,Type.message term) _atom]

type index_atom = [ `Index of (ord_eq,Vars.index) _atom]
                    
type trace_atom = [
  | `Timestamp of (ord,timestamp) _atom
  | `Index     of (ord_eq,Vars.index) _atom
  | `Happens   of Type.timestamp term
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
(** {2 Higher-order terms} *)

type hterm = 
  | Lambda of Vars.evars * message

(*------------------------------------------------------------------*)
(** {2 Builtins function symbols} *)

let mk f : fsymb = (f,[])

let f_diff = mk Symbols.fs_diff

(** Boolean function symbols, where booleans are typed as messages.
  * The true/false constants are used in message_of_formula,
  * and other symbols are used in an untyped way in Completion
  * (in some currently unused code). *)

let eboolean,emessage = Type.eboolean,Type.emessage

(** Boolean connectives *)

let f_false  = mk Symbols.fs_false
let f_true   = mk Symbols.fs_true
let f_and    = mk Symbols.fs_and
let f_or     = mk Symbols.fs_or
let f_impl   = mk Symbols.fs_impl
let f_not    = mk Symbols.fs_not
let f_ite    = mk Symbols.fs_ite

(** Fail *)

let f_witness = mk Symbols.fs_witness

(** Fail *)

let f_fail   = mk Symbols.fs_fail

(** Xor and its unit *)

let f_xor    = mk Symbols.fs_xor
let f_zero   = mk Symbols.fs_zero

(** Successor over natural numbers *)

let f_succ   = mk Symbols.fs_succ

(** Adversary function *)

let f_att    = mk Symbols.fs_att

(** Pairing *)

let f_pair   = mk Symbols.fs_pair
let f_fst    = mk Symbols.fs_fst
let f_snd    = mk Symbols.fs_snd

(** Boolean to Message *)
let f_of_bool = mk Symbols.fs_of_bool

(** Empty *)

let empty =
  let fty = Symbols.ftype_builtin Symbols.fs_empty in
  Fun (mk Symbols.fs_empty, fty, [])

(** Length *)

let f_len    = mk Symbols.fs_len
let f_zeroes = mk Symbols.fs_zeroes

(** Init action *)
let init = Action(Symbols.init_action,[])

(*------------------------------------------------------------------*)
(** {2 Smart constructors} *)

let mk_pred t = Pred t

let mk_var : type a. a Vars.var -> a term = fun v -> Var v

let mk_action a is = Action (a,is)

let mk_name n = Name n

let mk_macro ms l t = Macro (ms, l, t)

let mk_diff : type a. a term -> a term -> a term = fun a b -> Diff (a,b)

let mk_find is c t e = Find (is, c, t, e)

(*------------------------------------------------------------------*)
let mk_fun0 fs fty terms = Fun (fs, fty, terms)

let mk_fun table fname indices terms =
  let fty = Symbols.ftype table fname in
  Fun ((fname,indices), fty, terms)

let mk_fbuiltin = mk_fun Symbols.builtins_table

(*------------------------------------------------------------------*)
(** {3 For first-order formulas} *)

(** Smart constructors.
    The module is included after its definition. *)
module SmartConstructors = struct
  let mk_true  = mk_fbuiltin Symbols.fs_true  [] []
  let mk_false = mk_fbuiltin Symbols.fs_false [] []
  (** Some smart constructors are redefined later, after substitutions. *)

  let mk_not_ns term  = mk_fbuiltin Symbols.fs_not [] [term]

  let mk_and_ns  t0 t1 = mk_fbuiltin Symbols.fs_and  [] [t0;t1]
  let mk_or_ns   t0 t1 = mk_fbuiltin Symbols.fs_or   [] [t0;t1]
  let mk_impl_ns t0 t1 = mk_fbuiltin Symbols.fs_impl [] [t0;t1]


  let mk_not ?(simpl=true) t1 = match t1 with
    | Fun (fs,_,[t]) when fs = f_not && simpl -> t
    | t -> mk_not_ns t

  let mk_and ?(simpl=true) t1 t2 = match t1,t2 with
    | tt, t when tt = mk_true && simpl -> t
    | t, tt when tt = mk_true && simpl -> t
    | t1,t2 -> mk_and_ns t1 t2

  let mk_ands ?(simpl=true) ts = List.fold_left (mk_and ~simpl) mk_true ts

  let mk_or ?(simpl=true) t1 t2 = match t1,t2 with
    | tf, t when tf = mk_false && simpl -> t
    | t, tf when tf = mk_false && simpl -> t
    | t1,t2 -> mk_or_ns t1 t2

  let mk_ors ?(simpl=true) ts = List.fold_left (mk_or ~simpl) mk_false ts

  let mk_impl ?(simpl=true) t1 t2 = match t1,t2 with
    | tf, _ when tf = mk_false && simpl -> mk_true
    | tt, t when tt = mk_true && simpl -> t
    | t1,t2 -> mk_impl_ns t1 t2

  let mk_impls ?(simpl=true) ts t =
    List.fold_left (fun tres t0 -> (mk_impl ~simpl) t0 tres) t ts

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
end

include SmartConstructors

(*------------------------------------------------------------------*)
(** {3 For terms} *)

let mk_zero  = mk_fbuiltin Symbols.fs_zero  [] []
let mk_fail  = mk_fbuiltin Symbols.fs_fail  [] []

let mk_len term    = mk_fbuiltin Symbols.fs_len    [] [term]
let mk_zeroes term = mk_fbuiltin Symbols.fs_zeroes [] [term]

let mk_pair t0 t1 = mk_fbuiltin Symbols.fs_pair [] [t0;t1]

let mk_ite ?(simpl=true) c t e =
  match c with
  | t when t = mk_true  && simpl -> t
  | t when t = mk_false && simpl -> e
  | _ -> mk_fbuiltin Symbols.fs_ite [] [c;t;e]

let mk_of_bool t = mk_fbuiltin Symbols.fs_of_bool [] [t]

let mk_witness ty = 
  let fty = Type.mk_ftype 0 [] [] ty in
  Fun ((Symbols.fs_witness,[]), fty, [])


(*------------------------------------------------------------------*)
(** {3 For formulas} *)

let mk_timestamp_leq t1 t2 = match t1,t2 with
  | _, Pred t2' -> Atom(`Timestamp (`Lt, t1, t2'))
  | _ -> Atom(`Timestamp (`Leq, t1, t2))

(** Operations on vectors of indices of the same length. *)
let mk_indices_neq vect_i vect_j =
  List.fold_left
    (fun acc e -> mk_or acc e)
    mk_false
    (List.map2 (fun i j -> Atom (`Index (`Neq, i, j))) vect_i vect_j)

let mk_indices_eq ?(simpl=true) vect_i vect_j =
  List.fold_left
    (fun acc e -> mk_and acc e)
    mk_true
    (List.map2 (fun i j ->
         if i = j && simpl then mk_true else Atom (`Index (`Eq, i, j))
       ) vect_i vect_j)

let mk_lambda evs ht = match ht with
  | Lambda (evs', t) -> Lambda (evs @ evs', t) 

(*------------------------------------------------------------------*)
(** {2 Typing} *)

(*------------------------------------------------------------------*)
let rec kind : type a. a term -> a Type.kind =
  fun t -> match t with
    | Name _               -> Type.KMessage
    | Macro (s,_,_)        -> Type.KMessage
    | Seq _                -> Type.KMessage
    | Var v                -> Vars.kind v
    | Pred _               -> Type.KTimestamp
    | Action _             -> Type.KTimestamp
    | Diff (a, b)          -> kind a
    | Find (a, b, c, d)    -> Type.KMessage
    | Atom _               -> Type.KMessage
    | ForAll _             -> Type.KMessage
    | Exists _             -> Type.KMessage
    | Fun (_,fty,_)        -> Type.KMessage
        
(*------------------------------------------------------------------*)
let ty : type a. ?ty_env:Type.Infer.env -> a term -> a Type.t =
  fun ?ty_env t ->
  let must_close, ty_env = match ty_env with
    | None        -> true, Type.Infer.mk_env ()
    | Some ty_env -> false, ty_env
  in
  
  let rec ty : type a. a term -> a Type.t =
    fun t -> match t with
      | Fun (_,fty,terms) ->
        let fty = Type.open_ftype ty_env fty in
        let () =
          List.iter2 (fun arg arg_ty ->
              match Type.Infer.unify_leq ty_env (ty arg) arg_ty with
              | `Ok -> ()
              | `Fail -> assert false
            ) terms fty.Type.fty_args
        in
        fty.Type.fty_out

      | Name ns        -> ns.s_typ
      | Macro (s,_,_)  -> s.s_typ
        
      | Seq _                -> Type.Message
      | Var v                -> Vars.ty v
      | Pred _               -> Type.Timestamp
      | Action _             -> Type.Timestamp
      | Diff (a, b)          -> ty a
      | Find (a, b, c, d)    -> ty c
      | Atom _               -> Type.Boolean
      | ForAll _             -> Type.Boolean
      | Exists _             -> Type.Boolean

  in
  
  let tty = ty t in

  if must_close
  then Type.tsubst (Type.Infer.close ty_env) tty (* ty_env should be closed *)
  else tty

    
let ety ?ty_env t = Type.ETy (ty ?ty_env t)
    
(*------------------------------------------------------------------*)
exception Uncastable

let cast : type a b. a Type.kind -> b term -> a term =
  fun k t ->
  match Type.equalk_w (kind t) k with
  | Some Type.Type_eq -> t
  | None -> raise Uncastable

(*------------------------------------------------------------------*)
(** {2 Destructors} *)

let destr_fun ?fs = function
  | Fun (fs', _, l) when fs = None     -> Some l
  | Fun (fs', _, l) when fs = Some fs' -> Some l
  | _ -> None

let oas_seq0 = omap as_seq0
let oas_seq1 = omap as_seq1
let oas_seq2 = omap as_seq2

(*------------------------------------------------------------------*)
(** {3 For first-order formulas} *)

(** Smart destrucrots.
    The module is included after its definition. *)
module SmartDestructors = struct
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

  (*------------------------------------------------------------------*)
  let destr_false f = oas_seq0 (destr_fun ~fs:f_false f)
  let destr_true  f = oas_seq0 (destr_fun ~fs:f_true  f)

  let destr_not  f = oas_seq1 (destr_fun ~fs:f_not f)

  let destr_or   f = oas_seq2 (destr_fun ~fs:f_or   f)
  let destr_and  f = oas_seq2 (destr_fun ~fs:f_and  f)
  let destr_impl f = oas_seq2 (destr_fun ~fs:f_impl f)
  let destr_pair f = oas_seq2 (destr_fun ~fs:f_pair f)

  (*------------------------------------------------------------------*)
  (** for [fs] of arity 2, left associative *)
  let mk_destr_many_left fs =
    let rec destr l f =
      if l < 0 then assert false;
      if l = 1 then Some [f]
      else match destr_fun ~fs f with
        | None -> None
        | Some [f;g] -> omap (fun l -> l @ [g]) (destr (l-1) f)    
        | _ -> assert false
    in
    destr

  (** for [fs] of arity 2, right associative *)
  let mk_destr_many_right fs =
    let rec destr l f =
      assert (l > 0);
      if l = 1 then Some [f]
      else match destr_fun ~fs f with
        | None -> None
        | Some [f;g] -> omap (fun l -> f :: l) (destr (l-1) g)    
        | _ -> assert false
    in
    destr

  let destr_ors   = mk_destr_many_left  f_or
  let destr_ands  = mk_destr_many_left  f_and
  let destr_impls = mk_destr_many_right f_impl


  (*------------------------------------------------------------------*)      
  let destr_matom (form : message) : (ord_eq * message * message) option = 
    match form with
    | Atom (`Message (ord, a, b)) -> Some (ord, a, b)
    | _ -> None               

  (*------------------------------------------------------------------*)
  (** for any associative [fs] *)
  let mk_decompose fs =
    let rec decompose f = match destr_fun ~fs f with
      | None -> [f]
      | Some l -> List.concat_map decompose l
    in
    decompose

  let decompose_ors   = mk_decompose f_or  
  let decompose_ands  = mk_decompose f_and 

  let decompose_impls f =
    let rec decompose f = match destr_fun ~fs:f_impl f with
      | None -> [f]
      | Some [f;g] -> f :: decompose g
      | _ -> assert false
    in
    decompose f

  let decompose_impls_last f =
    let forms = decompose_impls f in
    let rec last = function
      | [] -> assert false
      | [f] -> [], f
      | f :: fs -> 
        let prems, goal = last fs in
        f :: prems, goal
    in 
    last forms

  (*------------------------------------------------------------------*)
  let is_false f = destr_false f <> None
  let is_true  f = destr_true f <> None

  let is_not f = destr_not f <> None

  let is_or   f = destr_or   f <> None
  let is_and  f = destr_and  f <> None
  let is_impl f = destr_impl f <> None
  let is_pair f = destr_pair f <> None

  let is_exists f = destr_exists f <> None
  let is_forall f = destr_forall f <> None
  let is_matom f  = destr_matom  f <> None

end

include SmartDestructors

(*------------------------------------------------------------------*)
let destr_var : type a. a term -> a Vars.var option = function
  | Var v -> Some v
  | _ -> None

(*------------------------------------------------------------------*)
let destr_action = function
  | Action (s,is) -> Some (s,is)
  | _ -> None

(*------------------------------------------------------------------*)
let is_binder : type a. a term -> bool = function 
  | ForAll _ | Exists _ | Find _ | Seq _ -> true
  | _ -> false

(*------------------------------------------------------------------*)
let as_ord_eq (ord : ord) : ord_eq = match ord with
  | `Eq -> `Eq
  | `Neq -> `Neq
  | _ -> assert false

(*------------------------------------------------------------------*)
(** {2 Printing} *)
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
  | Atom (`Happens _) -> true
  | _ as f ->  match destr_and f with
    | Some (l,r) -> is_and_happens l && is_and_happens r                        
    | _ -> false

(*------------------------------------------------------------------*)
(** Additional printing information *)
type pp_info = { styler : pp_info -> eterm -> Fmt.style list * pp_info; }

let default_pp_info = { styler = fun info _ -> [], info; }

let rec styled_list (styles : Fmt.style list) printer = 
  match styles with
  | [] -> printer
  | style :: styles -> styled_list styles (Fmt.styled style printer)


(* -------------------------------------------------------------------- *)
type assoc  = [`Left | `Right | `NonAssoc]
type fixity = [`Prefix | `Postfix | `Infix of assoc | `NonAssoc | `NoParens]

(* -------------------------------------------------------------------- *)
let pp_maybe_paren (c : bool) (pp : 'a Fmt.t) : 'a Fmt.t =
  if c then Fmt.parens pp else pp

let maybe_paren
    ~(inner : 'a * fixity) 
    ~(outer : 'a * fixity)
    ~(side  : assoc) 
    (pp : 'b Fmt.t) : 'b Fmt.t 
  =
  let noparens (pi, fi) (po, fo) side =
    match fo with
    | `NoParens -> true
    | _ ->
      match fi, side with
      | `Postfix     , `Left     -> true
      | `Prefix      , `Right    -> true
      | `Infix `Left , `Left     -> (pi = po) && (fo = `Infix `Left )
      | `Infix `Right, `Right    -> (pi = po) && (fo = `Infix `Right)
      | _            , `NonAssoc -> (pi = po) && (fi = fo)
      | _            , _         -> false
  in
  pp_maybe_paren (not (noparens inner outer side)) pp

let ite_fixity     = `F Symbols.fs_ite  , `Prefix
let pair_fixity    = `F Symbols.fs_pair , `NoParens
let iff_fixity     = `Iff               , `Infix `Right
let impl_fixity    = `F Symbols.fs_impl , `Infix `Right 
let or_fixity      = `F Symbols.fs_or   , `Infix `Left 
let and_fixity     = `F Symbols.fs_and  , `Infix `Left 
let not_fixity     = `F Symbols.fs_not  , `Prefix
let seq_fixity     = `Seq               , `Prefix
let find_fixity    = `Find              , `Prefix
let quant_fixity   = `Quant             , `NonAssoc
let macro_fixity   = `Macro             , `NoParens
let pred_fixity    = `Pred              , `NoParens
let diff_fixity    = `Diff              , `NoParens
let fun_fixity     = `Fun               , `NoParens
let happens_fixity = `Happens           , `NoParens
let ord_fixity ord = `Ord ord           , `NonAssoc

(*------------------------------------------------------------------*)

(** Applies the styling info in [info] *)
let rec pp : type a.
  pp_info ->
  (('b * fixity) * assoc) ->
  a term Fmt.t
  =
  fun info (outer,side) ppf t ->
  let styles, info = info.styler info (ETerm t) in
  styled_list styles (_pp info (outer, side)) ppf t

(** Core printing function *) 
and _pp : type a.
  pp_info ->
  (('b * fixity) * assoc) ->
  a term Fmt.t
  =
  fun info (outer, side) ppf t -> 
  let pp : type a. 
    (('b * fixity) * assoc)-> 
    a term Fmt.t 
    = 
    fun (outer,side) fmt t -> pp info (outer, side) fmt t
  in
  
  match t with
  | Var m -> Fmt.pf ppf "%a" Vars.pp m

  | Fun (s,_,[b;c; Fun (f,_,[])])
    when s = f_ite && f = f_zero ->
    let pp fmt () = 
      Fmt.pf ppf "@[<hov 2>if %a@ then@ %a@]"
        (pp (ite_fixity, `NonAssoc)) b 
        (pp (ite_fixity, `Right)) c
    in
    maybe_paren ~outer ~side ~inner:ite_fixity pp ppf ()

  | Fun (s,_,[b;Fun (f1,_,[]);Fun (f2,_,[])]) 
    when s = f_ite && f1 = f_true && f2 = f_false ->
    Fmt.pf ppf "%a" 
      (pp (ite_fixity, `NonAssoc)) b

  | Fun (s,_,[a;b;c]) when s = f_ite ->
    let pp fmt () =
      Fmt.pf ppf "@[<hov 0>@[<hov 2>if %a@ then@ %a@]@ @[<hov 2>else@ %a@]@]"
        (pp (ite_fixity, `NonAssoc)) a 
        (pp (ite_fixity, `NonAssoc)) b 
        (pp (ite_fixity, `Right)) c
    in
    maybe_paren ~outer ~side ~inner:ite_fixity pp ppf ()

  | Fun (s,_,terms) when s = f_pair ->
    Fmt.pf ppf "%a"
      (Utils.pp_ne_list
         "<@[<hov>%a@]>"
         (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,")
            (pp (pair_fixity, `NonAssoc))))
      terms


  | Fun (fa,_,[Fun (fi1,_,[bl1;br1]);
               Fun (fi2,_,[br2;bl2])]) 
    when fa = f_and && fi1 = f_impl && fi1 = f_impl &&
         bl1 = bl2 && br1 = br2 ->
    let pp fmt () = 
      Fmt.pf ppf "%a@ <=>@ %a]"
        (pp (iff_fixity, `Left)) bl1
        (pp (iff_fixity, `Right)) br1
    in
    maybe_paren ~outer ~side ~inner:iff_fixity pp ppf ()

  | Fun _ as f when is_and_happens f -> 
    pp_and_happens info ppf f

  (* only right-associate symbol we have *)
  | Fun ((s,is),_,[bl;br]) when (s = Symbols.fs_impl) ->
    assert (is = []);
    let pp fmt () = 
      Fmt.pf ppf "@[<0>%a %s@ %a@]"
        (pp ((`F s, `Infix `Right), `Left)) bl
        (Symbols.to_string s) 
        (pp ((`F s, `Infix `Right), `Right)) br
    in
    maybe_paren ~outer ~side ~inner:(`F s, `Infix `Right) pp ppf ()

  | Fun ((s,is),_,[bl;br]) when Symbols.is_infix s ->
    assert (is = []);
    let pp fmt () = 
      Fmt.pf ppf "@[<0>%a %s@ %a@]"
        (pp ((`F s, `Infix `Left), `Left)) bl
        (Symbols.to_string s) 
        (pp ((`F s, `Infix `Left), `Right)) br
    in
    maybe_paren ~outer ~side ~inner:(`F s, `Infix `Left) pp ppf ()

  | Fun (s,_,[b]) when s = f_not ->
    Fmt.pf ppf "@[<hov 2>not@ %a@]" (pp (not_fixity, `Right)) b

  | Fun _ as tt  when tt = mk_true ->  Fmt.pf ppf "true"             
  | Fun _  as tf when tf = mk_false -> Fmt.pf ppf "false"

  | Fun (f,_,[]) ->
    Fmt.pf ppf "%a" pp_fsymb f

  | Fun (f,_,[a]) ->
    Fmt.pf ppf "@[<hov 2>%a(@,%a)@]" 
      pp_fsymb f
      (pp (fun_fixity, `NonAssoc)) a

  | Fun (f,_,terms) ->
    Fmt.pf ppf "@[<hov>%a(%a)@]"
      pp_fsymb f
      (Utils.pp_ne_list
         "%a"
         (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,")
            (pp (fun_fixity, `NonAssoc))))
      terms

  | Name n -> pp_nsymb ppf n

  | Macro (m, l, ts) ->
    Fmt.pf ppf "@[%a%a@%a@]"
      pp_msymb m
      (Utils.pp_ne_list
         "(@[<hov>%a@])"
         (Fmt.list ~sep:Fmt.comma (pp (macro_fixity, `NonAssoc)))) l
      (pp (macro_fixity, `NonAssoc)) ts

  | Seq (vs, b) ->
    Fmt.pf ppf "@[<hov 2>seq(%a->@,%a)@]"
      Vars.pp_typed_list vs (pp (seq_fixity, `NonAssoc)) b

  | Pred ts -> 
    Fmt.pf ppf "pred(%a)" 
      (pp (pred_fixity, `NonAssoc)) ts

  | Action (symb,indices) ->
    Fmt.styled `Green
      (fun ppf () ->
         Fmt.pf ppf "%s%a" (Symbols.to_string symb) pp_indices indices)
      ppf ()

  | Diff (bl, br) ->
    Fmt.pf ppf "@[<hv 2>diff(@,%a,@,%a)@]"
      (pp (diff_fixity, `NonAssoc)) bl
      (pp (diff_fixity, `NonAssoc)) br

  | Find (b, c, d, Fun (f,_,[])) when f = f_zero ->
    let pp fmt () = 
      Fmt.pf ppf "@[<hov 0>\
                  @[<hov 2>try find %a such that@ %a@]@;<1 0>\
                  @[<hov 2>in@ %a@]@]"
        Vars.pp_list b
        (pp (find_fixity, `NonAssoc)) c
        (pp (find_fixity, `Right)) d
    in
    maybe_paren ~outer ~side ~inner:find_fixity pp ppf ()

  | Find (b, c, d, e) ->
    let pp fmt () = 
      Fmt.pf ppf "@[<hov 0>\
                  @[<hov 2>try find %a such that@ %a@]@;<1 0>\
                  @[<hov 0>\
                  @[<hov 2>in@ %a@]@;<1 0>\
                  @[<hov 2>else@ %a@]@]@]"
        Vars.pp_list b 
        (pp (find_fixity, `NonAssoc)) c
        (pp (find_fixity, `NonAssoc)) d
        (pp (find_fixity, `Right)) e
    in
    maybe_paren ~outer ~side ~inner:find_fixity pp ppf ()

  | ForAll (vs, b) ->
    let pp fmt () =
      Fmt.pf ppf "@[<2>forall (@[%a@]),@ %a@]"
        Vars.pp_typed_list vs 
        (pp (quant_fixity, `Right))  b
    in
    maybe_paren ~outer ~side ~inner:(`Quant, `Prefix) pp ppf ()

  | Exists (vs, b) ->
    let pp fmt () =
      Fmt.pf ppf "@[<2>exists (@[%a@]),@ %a@]"
        Vars.pp_typed_list vs 
        (pp (quant_fixity, `Right)) b
    in
    maybe_paren ~outer ~side ~inner:(`Quant, `Prefix) pp ppf ()

  | Atom a -> pp_generic_atom info ppf a
               
and pp_message_atom info ppf (`Message (o,tl,tr) : message_atom) =
  Fmt.pf ppf "@[%a %a@ %a@]" 
    (pp info (ord_fixity (o :> ord), `Left)) tl
    pp_ord o
    (pp info (ord_fixity (o :> ord), `Right)) tr
    
and pp_trace_atom info ppf : trace_atom -> unit = function
  | `Timestamp (o,tl,tr) ->
    Fmt.pf ppf "@[<hv>%a %a@ %a@]" 
      (pp info (ord_fixity o, `Left)) tl 
      pp_ord o
      (pp info (ord_fixity o, `Right)) tr
      
  | `Index (o,il,ir) ->
    Fmt.pf ppf "@[<hv>%a %a@ %a@]" Vars.pp il pp_ord o Vars.pp ir

  | `Happens a -> pp_happens info ppf [a]

and pp_generic_atom info ppf = function                   
  | #message_atom as a -> pp_message_atom info ppf a
                            
  | #trace_atom as a -> pp_trace_atom info ppf a

and pp_happens info ppf (ts : timestamp list) =
  Fmt.pf ppf "@[<hv 2>%a(%a)@]"
    pp_mname_s "happens"
    (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt ",@ ") 
       (pp info (happens_fixity, `NonAssoc))) ts
  
and pp_and_happens info ppf f =
  let rec collect acc = function
    | Atom (`Happens ts) -> ts :: acc
    | _ as f -> 
      let l, r = oget (destr_and f) in
      collect (collect acc l) r
  in

  pp_happens info ppf (collect [] f)

(*------------------------------------------------------------------*)
let pp_with_info : type a. pp_info -> Format.formatter -> a term -> unit = 
  fun info fmt t ->
  pp info ((`Toplevel, `NoParens), `NonAssoc) fmt t

let pp : type a. Format.formatter -> a term -> unit = 
  fun fmt t ->
  pp default_pp_info ((`Toplevel, `NoParens), `NonAssoc) fmt t

(*------------------------------------------------------------------*)

let pp_hterm fmt = function
  | Lambda (evs, t) -> 
    Fmt.pf fmt "@[<v 2>fun (@[%a@]) ->@ %a@]"
      Vars.pp_typed_list evs pp t

(*------------------------------------------------------------------*)
(** Literals. *)

type literal = [`Neg | `Pos] * generic_atom

type eq_literal = [`Pos | `Neg] * eq_atom

type trace_literal = [`Pos | `Neg] * trace_atom

let pp_literal fmt ((pn,at) : literal) =
  match pn with
  | `Pos -> Fmt.pf fmt "%a"    (pp_generic_atom default_pp_info) at
  | `Neg -> Fmt.pf fmt "¬(%a)" (pp_generic_atom default_pp_info) at

let pp_literals fmt (l : literal list) = 
  let sep fmt () = Fmt.pf fmt " ∧ " in
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
  | tf when tf = mk_false -> []
  | Atom at -> [`Pos, at]
  | Fun (fnot, _, [Atom at]) when fnot = f_not -> [`Neg, at]
  | Fun (fsor,_, [a; b])     when fsor = f_or -> aux a @ aux b
  | _ -> raise Not_a_disjunction in

  try Some (aux f) with Not_a_disjunction -> None

(*------------------------------------------------------------------*)
let form_to_literals (form : message) =
  let partial = ref false in
  let lits = 
    List.fold_left (fun acc -> function
        | Atom at -> (`Pos,at) :: acc
        | hyp ->
          match destr_not hyp with
          | Some (Atom at) -> (`Neg,at) :: acc
          | _ -> partial := true; acc
      ) [] (decompose_ands form)
  in
  if !partial then `Entails lits else `Equiv lits



(*------------------------------------------------------------------*)
let atom_triv = function
  | `Message   (`Eq,t1,t2) when t1=t2 -> true
  | `Timestamp (`Eq,t1,t2) when t1=t2 -> true
  | `Index     (`Eq,i1,i2) when i1=i2 -> true
  | _ -> false 

let f_triv = function
  | tt when tt = mk_true -> true
  | Atom atom -> atom_triv atom
  | _ -> false 

    
(*------------------------------------------------------------------*)
(** Declare input and output macros. *)
    
let mk s k = { s_symb = s; s_typ = k; s_indices = []; }

let in_macro    : msymb = mk Symbols.inp   Type.Message
let out_macro   : msymb = mk Symbols.out   Type.Message
let frame_macro : msymb = mk Symbols.frame Type.Message

let cond_macro : msymb = mk Symbols.cond Type.Boolean
let exec_macro : msymb = mk Symbols.exec Type.Boolean

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
      let term2 = cast (kind t1) term in
      if term2 = t1 then cast (kind term) t2 else assoc q term
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

let subst_evar (s : subst) (Vars.EVar v) : Vars.evar =
  Vars.EVar (subst_var s v)
  
let subst_isymb (s : subst) (symb : ('a,'b) isymb) : ('a,'b) isymb =
  { symb with s_indices = List.map (subst_var s) symb.s_indices }


let subst_macro (s : subst) isymb =
  { isymb with s_indices = List.map (subst_var s) isymb.s_indices }

(*------------------------------------------------------------------*)

let fv : 'a term -> Sv.t = fun term ->

  let of_list l = 
    let l = List.map (fun x -> Vars.EVar x) l in
    Sv.of_list l
  in

  let rec fv : type a. a term -> Sv.t = fun t -> 
    match t with
    | Action (_,indices) -> of_list indices
    | Var tv -> Sv.singleton (Vars.EVar tv) 
    | Pred ts -> fv ts
    | Fun ((_,indices), _,lt) ->
      Sv.union (of_list indices) (fvs lt)

    | Macro (s, l, ts) ->
      Sv.union
        (of_list s.s_indices)
        (Sv.union (fv ts) (fvs l))

    | Name s -> of_list s.s_indices

    | Diff (a, b) -> fvs [a;b]

    | Find (a, b, c, d) ->
      Sv.union
        (Sv.diff (fvs [b;c]) (of_list a))
        (fv d)

    | Atom a -> generic_atom_vars a 

    | Seq    (a, b)
    | ForAll (a, b)
    | Exists (a, b) -> Sv.diff (fv b) (Sv.of_list a)

  and fvs : type a. a term list -> Sv.t = fun terms ->
    List.fold_left (fun sv x -> Sv.union (fv x) sv) Sv.empty terms
    
  and message_atom_vars (`Message (ord, a1, a2)) =
   Sv.union (fv a1) (fv a2)

  and trace_atom_vars at = match at with
    | `Timestamp (ord, ts, ts') ->
      Sv.union (fv ts) (fv ts')
    | `Index (ord, i, i') ->
      Sv.union (fv (Var i)) (fv (Var i'))
    | `Happens ts -> fv ts
                       
  and generic_atom_vars t = match t with
    | #message_atom as a -> message_atom_vars a 
    | #trace_atom as a -> trace_atom_vars a 
  in

  fv term

let get_vars t = fv t |> Sv.elements

(*------------------------------------------------------------------*)
(** {2 Substitutions} *)

(** given a variable [x] and a subst [s], remove from [s] all
    substitution [v->_]. *)
let filter_subst (var:Vars.evar) (s:subst) =
  let s = 
    List.fold_left (fun acc (ESubst (x, y)) ->
        if not (Sv.mem var (fv x))
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
    Sv.union supp (fv t)) Sv.empty s

let is_binder : type a. a term -> bool = function
  | Seq _ | ForAll _ | Exists _ | Find _ -> true
  | _ -> false

let rec subst : type a. subst -> a term -> a term = fun s t ->
  if s = [] ||
     (is_binder t && 
      is_var_subst s && 
      Sv.disjoint (subst_support s) (fv t))
  then t
  else
    let new_term : a term =
      match t with
      | Fun ((fs,is), fty, lt) ->
        Fun ((fs, List.map (subst_var s) is), fty, List.map (subst s) lt)

      | Name symb -> 
        Name { symb with s_indices = List.map (subst_var s) symb.s_indices}

      | Macro (m, l, ts) ->
        Macro (subst_macro s m, List.map (subst s) l, subst s ts)

      | Var m -> Var m
      | Pred ts -> Pred (subst s ts)
      | Action (a,indices) -> Action (a, List.map (subst_var s) indices)
      | Diff (a, b) -> Diff (subst s a, subst s b)
      | Atom a-> Atom (subst_generic_atom s a)

      | Seq ([], f) -> Seq ([], subst s f)

      | Seq ([a], f) -> 
        let a, s = subst_binding a s in
        let f = subst s f in
        Seq ([a],f)

      | Seq (a :: vs, f) -> 
        let a, s = subst_binding a s in
        let f = subst s (Seq (vs,f)) in
        let vs, f = match f with
          | Seq (vs, f) -> vs, f
          | _ -> assert false in
        Seq (a :: vs,f)

      | ForAll ([], f) -> subst s f

      | ForAll (a :: vs, f) ->
        let a, s = subst_binding a s in
        let f = subst s (ForAll (vs,f)) in
        mk_forall [a] f

      | Exists ([], f) -> subst s f

      | Exists (a :: vs, f) ->
        let a, s = subst_binding a s in
        let f = subst s (Exists (vs,f)) in
        mk_exists [a] f

      | Find ([], b, c, d) -> Find ([], subst s b, subst s c, subst s d) 

      | Find (v :: vs, b, c, d) -> 
        (* used because [v :: vs] are not bound in [d]  *)
        let dummy = mk_zero in

        let v, s = subst_binding (Vars.EVar v) s in
        let f = subst s (Find (vs, b, c, dummy)) in
        let v = Vars.ecast v Type.KIndex in
        match f with
        | Find (vs, b, c, _) -> Find (v :: vs, b, c, subst s d) 
        | _ -> assert false
    in 
    assoc s new_term

and subst_binding : Vars.evar -> subst -> Vars.evar * subst =
  fun var s ->
  (* clear [v] entries in [s] *)
  let s = filter_subst var s in

  let right_fv = 
    List.fold_left (fun acc (ESubst (x, y)) -> 
        Sv.union acc (fv y)
      ) Sv.empty s in

  let all_vars = 
    List.fold_left (fun acc (ESubst (x, y)) -> 
        Sv.union acc (fv x)
      ) right_fv s in

  let env = ref (Vars.of_list (Sv.elements all_vars)) in

  (* if [v] is appears in the RHS of [s], refresh [v] carefully *)
  let var, s = 
    if Sv.mem var right_fv 
    then 
      match var with 
      | Vars.EVar v ->
        let new_v = Vars.fresh_r env v in
        let s = (ESubst (Var v,Var new_v)) :: s in
        ( Vars.EVar new_v, s)
    else ( var, s ) in
  
  var, s

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
    | Macro (is, terms, ts') ->
      let terms' = List.map subst_term terms in
      begin match Symbols.Macro.get_all is.s_symb table with
      | Symbols.State _, _ ->
        if (List.mem (Symbols.to_string is.s_symb) l && ts=ts')
        then Macro(is, terms', ts')
        else Macro(is, terms', Pred(ts'))

      | _ -> Macro(is, terms', ts')
      end

    | Fun (f,fty,terms)  -> Fun    (f, fty, List.map subst_term terms)
    | Seq (a, b)         -> Seq    (a, subst_term b)
    | Diff (a, b)        -> Diff   (subst_term a, subst_term b)
    | Find (vs, b, t, e) -> Find   (vs, subst_term b, subst_term t, subst_term e)
    | ForAll (vs, b)     -> ForAll (vs, subst_term b)
    | Exists (vs, b)     -> Exists (vs, subst_term b)
    | Atom a             -> Atom   (subst_generic_atom a)
    | _ -> t

  and subst_message_atom (`Message (ord, a1, a2)) =
    `Message (ord, subst_term a1, subst_term a2)

  and subst_generic_atom a = match a with
    | #message_atom as a -> (subst_message_atom a :> generic_atom)
    | _ -> a
  in

  subst_term t

let rec subst_ht s ht = match ht with
  | Lambda (ev :: evs, t) ->
    let ev, s = subst_binding ev s in
    mk_lambda [ev] (subst_ht s (Lambda (evs, t)))
  | Lambda ([], t) -> Lambda ([], subst s t)

(*------------------------------------------------------------------*)
type refresh_arg = [`Global | `InEnv of Vars.env ref ]

let refresh_var (arg : refresh_arg) v = 
  match arg with
  | `Global    -> Vars.make_new_from v
  | `InEnv env -> Vars.fresh_r env v

(* the substitution must be build reversed w.r.t. vars, to handle capture *)
let refresh_vars (arg : refresh_arg) vars =
  let vars' = List.map (refresh_var arg) vars in
  let subst = 
    List.rev_map2 (fun v v' -> ESubst (Var v, Var v')) vars vars' 
  in
  vars', subst

(* the substitution must be build reversed w.r.t. vars, to handle capture *)
let erefresh_vars (arg : refresh_arg) evars =
  let l = 
    List.rev_map (fun (Vars.EVar v) -> 
        let v' = refresh_var arg v in
        Vars.EVar v', ESubst (Var v, Var v') 
      ) evars
  in
  let vars, subst = List.split l in
  List.rev vars, subst

let refresh_vars_env env vs = 
  let env = ref env in
  let vs, s = refresh_vars (`InEnv env) vs in
  !env, vs, s

let erefresh_vars_env env vs = 
  let env = ref env in
  let vs, s = erefresh_vars (`InEnv env) vs in
  !env, vs, s

(*------------------------------------------------------------------*)

(** [app func t] applies [func] to [t]. [func] must preserve types. *)
let app : type a. (eterm -> eterm) -> a term -> a term = 
  fun func x ->
  let ETerm x0 = func (ETerm x) in
  cast (kind x) x0
  
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
  | Action _ -> t
  | Name _   -> t
  | Var _    -> t
      
  | Fun (f,fty,terms) -> Fun (f, fty, List.map func terms)
  | Macro (m, l, ts)  -> Macro (m, List.map func l, func ts) 
  | Seq (vs, b)       -> Seq (vs, func b)      
  | Pred ts           -> Pred (func ts)                 

  | Diff (bl, br)     -> 
    let bl = func bl in
    let br = func br in
    Diff (bl, br)      

  | Find (b, c, d, e) -> 
    let c = func c 
    and d = func d 
    and e = func e in
    Find (b, c, d, e)
        
  | ForAll (vs, b)    -> ForAll (vs, func b)      
  | Exists (vs, b)    -> Exists (vs, func b)

  | Atom at -> Atom (atom_map func0 at)

let tmap_fold : type a. ('b -> eterm -> 'b * eterm) -> 'b -> a term -> 'b * a term = 
  fun func b t ->
  let bref = ref b in
  let g t = 
    let b, t = func !bref t in
    bref := b;
    t
  in
  let t = tmap g t in
  !bref, t   

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
(** {2 Smart constructors and destructors -- Part 2} *)

module type SmartFO = sig
  type form

  (** {3 Constructors} *)
  val mk_true    : form
  val mk_false   : form

  val mk_not   : ?simpl:bool -> form              -> form
  val mk_and   : ?simpl:bool -> form      -> form -> form
  val mk_ands  : ?simpl:bool -> form list         -> form
  val mk_or    : ?simpl:bool -> form      -> form -> form
  val mk_ors   : ?simpl:bool -> form list         -> form
  val mk_impl  : ?simpl:bool -> form      -> form -> form
  val mk_impls : ?simpl:bool -> form list -> form -> form

  val mk_forall : ?simpl:bool -> Vars.evars -> form -> form
  val mk_exists : ?simpl:bool -> Vars.evars -> form -> form

  (*------------------------------------------------------------------*)
  (** {3 Destructors} *)

  val destr_forall : form -> (Vars.evar list * form) option
  val destr_exists : form -> (Vars.evar list * form) option

  (*------------------------------------------------------------------*)
  val destr_false : form ->         unit  option
  val destr_true  : form ->         unit  option
  val destr_not   : form ->         form  option
  val destr_and   : form -> (form * form) option
  val destr_or    : form -> (form * form) option
  val destr_impl  : form -> (form * form) option

  (*------------------------------------------------------------------*)
  val is_false  : form -> bool
  val is_true   : form -> bool
  val is_not    : form -> bool
  val is_and    : form -> bool
  val is_or     : form -> bool
  val is_impl   : form -> bool
  val is_forall : form -> bool
  val is_exists : form -> bool
  val is_matom  : form -> bool

  (*------------------------------------------------------------------*)
  (** left-associative *)
  val destr_ands  : int -> form -> form list option
  val destr_ors   : int -> form -> form list option
  val destr_impls : int -> form -> form list option

  (*------------------------------------------------------------------*)
  val destr_matom : form -> (ord_eq * message * message) option 

  (*------------------------------------------------------------------*)
  val decompose_forall : form -> Vars.evar list * form
  val decompose_exists : form -> Vars.evar list * form

  (*------------------------------------------------------------------*)
  val decompose_ands  : form -> form list 
  val decompose_ors   : form -> form list 
  val decompose_impls : form -> form list 

  val decompose_impls_last : form -> form list * form
end

module Smart : SmartFO with type form = message = struct
  type form = message

  include SmartConstructors
  include SmartDestructors

  (* FIXME: improve variable naming (see mk_seq) *)
  let mk_forall ?(simpl=false) l f = 
    let l = 
      if simpl then
        let fv = fv f in
        List.filter (fun v -> Sv.mem v fv) l 
      else l
    in
    mk_forall l f

  (* FIXME: improve variable naming (see mk_seq) *)
  let mk_exists ?(simpl=false) l f = 
    let l = 
      if simpl then
        let fv = fv f in
        List.filter (fun v -> Sv.mem v fv) l 
      else l
    in
    mk_exists l f

end

include Smart


let mk_atom : type a b. ord -> a term -> b term -> message =
  fun ord t1 t2 ->
  match kind t1, kind t2 with
  | Type.KMessage, Type.KMessage ->    
    Atom (`Message (as_ord_eq ord, t1, t2))

  | Type.KIndex, Type.KIndex ->    
    let v1, v2 = oget (destr_var t1), oget (destr_var t2) in
    Atom (`Index (as_ord_eq ord, v1, v2))

  | Type.KTimestamp, Type.KTimestamp ->    
    Atom (`Timestamp (ord, t1, t2))

  | _ -> assert false

let mk_happens t = Atom (`Happens t)

let mk_atom1 at = Atom at

let mk_seq0 ?(simpl=false) (is : Vars.evars) term = 
  let is = 
    if simpl then
      let term_fv = fv term in
      List.filter (fun i ->
          Sv.mem i term_fv
        ) is
    else is
  in
  match is with
  | [] -> term
  | _ -> Seq (is, term)

(* only refresh necessary vars, hence we need an environment *)
let mk_seq env (is : Vars.evars) term =
  let env =
    let env_vars = Sv.of_list (Vars.to_list env) in
    let term_vars = fv term in
    let vars = Sv.elements (Sv.inter env_vars term_vars) in
    ref (Vars.of_list vars)
  in

  let is, s = erefresh_vars (`InEnv env) is in
  let term = subst s term in

  match is with
  | [] -> term
  | _ -> Seq (is, term)


(*------------------------------------------------------------------*)
(** {2 Apply} *)

let apply_ht (ht : hterm) (terms : eterm list) = match ht with
  | Lambda (evs, t) ->
    assert (List.length terms <= List.length evs);
    let evs0, evs1 = List.takedrop (List.length terms) evs in

    let evs0, s = erefresh_vars `Global evs0 in
    let ht = subst_ht s (Lambda (evs1, t)) in

    let s_app = 
      List.map2 (fun (Vars.EVar v) (ETerm t) -> 
          ESubst (Var v, cast (Vars.kind v) t)
        ) evs0 terms 
    in
    subst_ht s_app ht
    


(*------------------------------------------------------------------*)
(** {2 Type substitution} *)

let tsubst : type a. Type.tsubst -> a term -> a term = 
  fun ts t ->
  
  (* no need to substitute in the types of [Name], [Macro], [Fun] *)
  let rec tsubst : type a. a term -> a term = function
    | Var v -> Var (Vars.tsubst ts v)
    | ForAll (vs, f) -> ForAll (List.map (Vars.tsubst_e ts) vs, tsubst f)
    | Exists (vs, f) -> Exists (List.map (Vars.tsubst_e ts) vs, tsubst f)
    | _ as term -> tmap (fun (ETerm t) -> ETerm (tsubst t)) term
  in

  tsubst t

let tsubst_ht (ts : Type.tsubst) (ht : hterm) : hterm =
  match ht with
  | Lambda (vs, f) -> Lambda (List.map (Vars.tsubst_e ts) vs, tsubst ts f)

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
    | tt when tt = mk_true  -> mk_false
    | tf when tf = mk_false -> mk_true
    | Fun (fs, _, [a;b]) when fs = f_and  -> mk_or  (not_simpl a) (not_simpl b)
    | Fun (fs, _, [a;b]) when fs = f_or   -> mk_and (not_simpl a) (not_simpl b)
    | Fun (fs, _, [a;b]) when fs = f_impl -> mk_and a (not_simpl b)
    | Fun (fs, _, [f]) when fs = f_not -> f
    | Atom atom ->
      begin
        match atom with
        | (`Message _                 as at)
        | (`Index _                   as at)
        | (`Timestamp (#ord_eq, _, _) as at) ->
          Atom (not_eq_atom at :> generic_atom)

        | `Timestamp _ | `Happens _  -> mk_not (Atom atom)
      end          
    | m -> mk_not m

let is_pure_timestamp (t : message) =
  let rec pure_ts = function
    | Atom (`Index _) 
    | Atom (`Happens _)
    | Atom (`Timestamp _) -> true

    | Fun (fs, _, [t1; t2])
      when fs = f_or || fs = f_and || fs = f_impl ->
      pure_ts t1 && pure_ts t2

    | Fun (fs, _, [t]) when fs = f_not -> pure_ts t

    | Fun (fs, _, []) -> true

    | ForAll (_, t)
    | Exists (_, t) -> pure_ts t

    | _ -> false
  in
  pure_ts t
                                                

(*------------------------------------------------------------------*)
(** {2 Projection} *)

type projection = PLeft | PRight | PNone

let pp_projection fmt = function
  | PLeft  -> Fmt.pf fmt "Left"
  | PRight -> Fmt.pf fmt "Right"
  | PNone  -> Fmt.pf fmt "None"

let pi_term ~projection term =

  let rec pi_term : type a. projection -> a term -> a term = fun s t ->
  match t with
  | Fun (f,fty,terms) -> Fun (f, fty, List.map (pi_term s) terms)
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
  | Find (vs, b, t, e) -> Find (vs, pi_term s b, pi_term s t, pi_term s e)
  | ForAll (vs, b) -> ForAll (vs, pi_term s b)
  | Exists (vs, b) -> Exists (vs, pi_term s b)
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
  | Fun (f,fty,l), Fun (f',fty',l') when f = f' ->
    Fun (f, fty, List.map2 diff l l')

  | Name n, Name n' when n=n' -> Name n

  | Macro (m,l,ts), Macro (m',l',ts') when m=m' && ts=ts' ->
      Macro (m, List.map2 diff l l', ts)

  | Pred t, Pred t' -> Pred (diff t t')

  | Action (a,is), Action (a',is') when a=a' && is=is' -> Action (a,is)

  | Var x, Var x' when x=x' -> Var x

  | Find (is,c,t,e), Find (is',c',t',e') when is=is' ->
      Find (is, diff c c', diff t t', diff e e')

  | Atom a, Atom a' when a = a' -> Atom a

  | Atom (`Message (o,u,v)), Atom (`Message (o',u',v')) when o = o' ->
    Atom (`Message (o, diff u u', diff v v'))
      
  | ForAll (vs,f), ForAll (vs',f') when vs=vs' -> ForAll (vs, diff f f')
  | Exists (vs,f), Exists (vs',f') when vs=vs' -> Exists (vs, diff f f')
                                                    
  | t    ,t'      -> diff t t'

let make_bi_term  : type a. a term -> a term -> a term = fun t1 t2 ->
  head_normal_biterm (Diff (t1, t2))


(*------------------------------------------------------------------*)
(** {2 Sets and Maps } *)

module T = struct
  type t = eterm
  let compare = Stdlib.compare
end

module Mt = Map.Make (T)
module St = Set.Make (T)


(*------------------------------------------------------------------*)
(** {2 Matching information for error messages} *)

(* TODO: this should'nt be here *)

type match_info = 
  | MR_ok                         (* term matches *)
  | MR_check_st of message list   (* need to look at subterms *)
  | MR_failed                     (* term does not match *)

type match_infos = match_info Mt.t

let pp_match_info fmt = function
  | MR_ok              -> Fmt.pf fmt "ok"
  | MR_check_st terms  -> Fmt.pf fmt "check subterms %a" (Fmt.list pp) terms
  | MR_failed          -> Fmt.pf fmt "failed"

let pp_match_infos fmt minfos = 
  let pp_one fmt (ETerm t, mi) = Fmt.pf fmt "%a → %a" pp t pp_match_info mi in
  Fmt.pf fmt "@[<v 0>%a@]" (Fmt.list pp_one) (Mt.bindings minfos)

let match_infos_to_pp_info (minfos : match_infos) : pp_info = 
  let styler info (t : eterm) : Fmt.style list * pp_info = 
    match Mt.find_opt t minfos with
    | None               -> [], info
    | Some MR_ok         -> [(* Fmt.(`Bg `Green) *)],  default_pp_info
    | Some MR_check_st _ -> [(* Fmt.(`Bg `Yellow) *)], info
    | Some MR_failed     -> [Fmt.(`Bg `Red)],    info
  in
  { styler }

(*------------------------------------------------------------------*)
(** {2 Tests} *)

let () =
  let mkvar x s = Var (snd (Vars.make `Approx Vars.empty_env s x)) in
  Checks.add_suite "Head normalization" [
    "Macro, different ts", `Quick, begin fun () ->
      let ts = mkvar "ts" Type.Timestamp in
      let ts' = mkvar "ts'" Type.Timestamp in
      let m = in_macro in
      let t = Diff (Macro (m,[],ts), Macro (m,[],ts')) in
      let r = head_normal_biterm t in
      assert (r = t)
    end ;
    "Boolean operator", `Quick, begin fun () ->
      let f = mkvar "f" Type.Boolean in
      let g = mkvar "g" Type.Boolean in
      let f' = mkvar "f'" Type.Boolean in
      let g' = mkvar "g'" Type.Boolean in
      let t = Diff (mk_and f g, mk_and f' g') in
        assert (head_normal_biterm t = mk_and (Diff (f,f')) (Diff (g,g')))
    end ;
  ] ;
  Checks.add_suite "Projection" [
    "Simple example", `Quick, begin fun () ->
      let a = mkvar "a" Type.Message in
      let b = mkvar "b" Type.Message in
      let c = mkvar "c" Type.Message in

      let fty = Type.mk_ftype 0 [] [Type.Message;Type.Message] Type.Message in  

      let def = fty, Symbols.Abstract `Prefix in
      let table,f =
        Symbols.Function.declare_exact 
          Symbols.builtins_table (L.mk_loc L._dummy "f") def in
      let fty = Type.mk_ftype 0 [] [] Type.Message in
      let f x = Fun ((f,[]),fty,[x]) in
      let t = Diff (f (Diff(a,b)), c) in
      let r = head_pi_term PLeft t in
        assert (pi_term  ~projection:PLeft t = f a) ;
        assert (r = f (Diff (a,b)))
    end ;
  ]
