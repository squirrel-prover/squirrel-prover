open Vars
open Action
(** Terms and formulas for the Meta-BC logic.
  *
  * This modules describes the syntax of the logic. It does not
  * provide low-level representations, normal forms, etc. that
  * are to be used in automated reasoning, nor does it provide
  * representations necessary for the front-end involving
  * processes, axioms, etc. *)

(** Timestamps represent positions in a trace *)

module TParam : VarParam =
struct
  let default_string = "tau"
  let cpt = ref 0
end

module Tvar = Var(TParam)

type tvar = Tvar.t

type timestamp =
  | TVar of tvar
  | TPred of timestamp
  | TName of action

let rec pp_timestamp ppf = function
  | TVar tv -> Tvar.pp ppf tv
  | TPred ts -> Fmt.pf ppf "@[<hov>p(%a)@]" pp_timestamp ts
  | TName a -> Action.pp_action ppf a

(** Messages variables for formulas **)
                 
module MParam : VarParam =
struct
  let default_string = "mess"
  let cpt = ref 0
end

module Mvar = Var(MParam)

type mvar = Mvar.t

(** Names represent random values, uniformly sampled by the process.
  * A name symbol is derived from a name (from a finite set) and
  * a list of indices. *)

type name = Name of string

(* TODO declarations, freshness conditions ? *)
let mk_name x = Name x
let fresh_name x = Name x

let pp_name ppf = function Name s -> (Utils.kw `Yellow) ppf ("n!"^s)

type nsymb = name * index list

let pp_nsymb ppf (n,is) =
  if is <> [] then Fmt.pf ppf "%a[%a]" pp_name n Index.pp_list is
  else Fmt.pf ppf "%a" pp_name n

(** Function symbols are built from a name (from a finite set)
  * and a list of indices.
  *
  * TODO must include builtins such as if-then-else, equality, successor, xor ...
  * Adrien: already added some
  * Some keywords should probably be forbidden, e.g. "input", "output"
  *)

type fname = Fname of string

let pp_fname ppf = function Fname s -> (Utils.kw `Bold) ppf s

type fsymb = fname * index list

let pp_fsymb ppf (fn,is) = match is with
  | [] -> Fmt.pf ppf "%a" pp_fname fn
  | _ -> Fmt.pf ppf "%a[%a]" pp_fname fn Index.pp_list is

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

(** Memory cells are represented by state variable, themselves
  * derived from a name (from a finite set) and indices.
  *
  * TODO simplify design to merge name, function and state names ?
  *)

type sname = Sname of string
let mk_sname x = Sname x

let pp_sname ppf = function Sname s -> (Utils.kw `Red) ppf ("s!"^s)

type state = sname * index list

let pp_state ppf (sn,is) =
  if is <> [] then Fmt.pf ppf "%a(%a)" pp_sname sn Index.pp_list is
  else Fmt.pf ppf "%a" pp_sname sn

(** Type of macros name *)
type mname = string
type msymb = mname * index list

let pp_mname ppf s =
  let open Fmt in
  (styled `Bold (styled `Magenta Utils.ident)) ppf ("m!"^s)

let pp_msymb ppf (m,is) =
  Fmt.pf ppf "%a%a"
    pp_mname m
    (Utils.pp_ne_list "(%a)" Index.pp_list) is

(** Terms *)
type term =
  | Fun of fsymb * term list
  | Name of nsymb
  | MVar of mvar
  | State of state * timestamp
  (* | Input of timestamp *)
  | Macro of msymb * timestamp

let dummy = Fun ((Fname "_",[]),[])

let rec pp_term ppf = function
  | Fun (f,terms) ->
      Fmt.pf ppf "%a%a"
        pp_fsymb f
        (Utils.pp_ne_list
           "(@[<hov>%a@])"
           (Fmt.list ~sep:Fmt.comma pp_term)) terms
  | Name n -> pp_nsymb ppf n
  | State (s,ts) -> Fmt.pf ppf "@[%a@%a@]" pp_state s pp_timestamp ts
  | Macro (m,ts) -> Fmt.pf ppf "@[%a@%a@]" pp_msymb m pp_timestamp ts
  | MVar m -> Fmt.pf ppf "%a" Mvar.pp m                     
  (* | Input ts -> Fmt.pf ppf "@[in@%a@]" pp_timestamp ts *)

type t = term

let macros : (string, (timestamp -> index list -> term)) Hashtbl.t =
  Hashtbl.create 97

let built_ins = ["input";"output"]

(** [is_built_in mn] returns true iff [mn] is a built-in.  *)
let is_built_in mn = List.mem mn built_ins

let is_declared mn =
  if Hashtbl.mem macros mn || List.mem mn built_ins then mn
  else raise Not_found

let declare_macro mn f =
  assert (not (is_built_in mn) && not (Hashtbl.mem macros mn)) ;
  Hashtbl.add macros mn f;
  mn                            (* TODO: refresh if already there *)


(** Return the term corresponding to the declared macro, except for the
    built-ins "input" and "output". *)
let macro_declaration mn =
  if is_built_in mn then
    raise @@ Failure "look-up of a built-in declaration"
  else Hashtbl.find macros mn

let mk_mname mn indices = (mn,indices)

let in_macro = ("input",[])
let out_macro = ("output",[])

(** Boolean formulas *)
type 'a bformula =
  | And of 'a bformula * 'a bformula
  | Or of 'a bformula * 'a bformula
  | Not of 'a bformula
  | Impl of 'a bformula * 'a bformula
  | Atom of 'a
  | True
  | False

let rec pp_bformula pp_atom ppf = function
  | And (bl,br) ->
    Fmt.pf ppf "@[<hv>(%a && %a)@]"
      (pp_bformula pp_atom) bl (pp_bformula pp_atom) br
  | Or (bl,br) ->
    Fmt.pf ppf "@[<hv>(%a || %a)@]"
      (pp_bformula pp_atom) bl (pp_bformula pp_atom) br
  | Impl (bl,br) ->
    Fmt.pf ppf "@[<hv>(%a -> %a)@]"
      (pp_bformula pp_atom) bl (pp_bformula pp_atom) br
  | Not b ->
    Fmt.pf ppf "@[<hv>not(%a)@]" (pp_bformula pp_atom) b
  | Atom a -> pp_atom ppf a
  | True -> Fmt.pf ppf "true"
  | False -> Fmt.pf ppf "false"

(** [atoms b] returns the list of atoms appearing in [b] *)
let atoms b =
  let rec aux acc = function
    | True | False -> acc
    | And (a,b) | Or (a,b) | Impl (a,b) -> aux (aux acc a) b
    | Not a -> aux acc a
    | Atom at -> at :: acc in

  aux [] b



(** Evaluate trivial subformula. *)
let rec triv_eval = function
  | Or (a,b) ->
    begin match triv_eval a, triv_eval b with
      | _, True | True,_ -> True
      | _ as te, False | False, (_ as te) -> te
      | _ as ta, (_ as tb) -> Or (ta, tb) end

  | And (a,b) ->
    begin match triv_eval a, triv_eval b with
      | _ as te, True | True, (_ as te) -> te
      | _, False | False,_ -> False
      | _ as ta, (_ as tb) -> And (ta, tb) end

  | Impl (a,b) ->
    begin match triv_eval a, triv_eval b with
      | _, True | False, _ -> True
      | True, (_ as te) -> te
      | _ as ta, (_ as tb) -> Impl (ta, tb) end

  | Not a -> begin match triv_eval a with
      | True -> False
      | False -> True
      | _ as ta -> Not ta end

  | _ as a -> a

(** [simpl_formula nlit b] simplifies the bformula [b], using [nlit] to
    transform negative atoms into positive atoms *)
let simpl_formula nlit b =
  let rec simp flip = function
    | Atom a -> if flip then Atom (nlit a) else Atom a
    | True -> if flip then False else True
    | False -> if flip then True else False
    | Or (l,r) ->
      if flip then And (simp flip l, simp flip r)
      else Or (simp flip l, simp flip r)
    | And (l,r) ->
      if flip then Or (simp flip l, simp flip r)
      else And (simp flip l, simp flip r)
    | Impl (l,r) ->  Or (Not l, r) |> simp flip
    | Not b -> simp (not flip) b in
  simp false b |> triv_eval


(** [bf_dnf nlit b] puts the  bformula [b] in DNF, using [nlit] to transform
    negative atoms into positive atoms *)
let bf_dnf : ('a -> 'a) -> 'a bformula -> 'a list list = fun nlit b ->

  let rec dnf = function
    | Or (a,b) -> dnf a @ dnf b
    | False -> []
    | True -> [[]]
    | Atom a -> [[a]]
    | And (a,b) ->
      let bdnf = dnf b in
      List.fold_left (fun acc c ->
          (List.fold_left (fun acc c' ->
               (c @ c') :: acc) acc bdnf))
        [] (dnf a)
    | Impl _ | Not _ -> assert false in

  simpl_formula nlit b |> dnf


(** Atoms *)

type ord = Eq | Neq | Leq | Geq | Lt | Gt

type 'a _atom = ord * 'a * 'a

type atom = term _atom

type fact = atom bformula

let pp_ord ppf = function
  | Eq -> Fmt.pf ppf "="
  | Neq -> Fmt.pf ppf "<>"
  | Leq -> Fmt.pf ppf "<="
  | Geq -> Fmt.pf ppf ">="
  | Lt -> Fmt.pf ppf "<"
  | Gt -> Fmt.pf ppf ">"

let not_ord o = match o with
  | Eq -> Neq
  | Neq -> Eq
  | Leq -> Gt
  | Geq -> Lt
  | Lt -> Geq
  | Gt -> Leq

let pp_atom ppf (o,tl,tr) =
    Fmt.pf ppf "@[<h>%a %a %a@]" pp_term tl pp_ord o pp_term tr

let pp_fact = pp_bformula pp_atom

(** Negate the atom *)
let not_xpred (o,l,r) = (not_ord o, l, r)

let simpl_fact f = simpl_formula not_xpred f

(** Replace an atom by an equivalent list of atoms using only Eq,Neq and Leq *)
let norm_xatom (o,l,r) = match o with
  | Eq | Neq | Leq -> [(o,l,r)]
  | Geq -> [(Leq,r,l)]
  | Lt -> (Leq,l,r) :: [(Neq,l,r)]
  | Gt -> (Leq,r,l) :: [(Neq,r,l)]

let add_xeq od xeq (eqs,leqs,neqs) = match od with
  | Eq -> (xeq :: eqs, leqs, neqs)
  | Leq -> (eqs, xeq :: leqs, neqs)
  | Neq -> (eqs, leqs, xeq :: neqs)
  | _ -> raise (Failure ("add_xeq: bad comparison operator"))


(** Constraints:
    - [Pind (o,i,i')] : [o] must be either [Eq] or [Neq] *)
type tatom =
  | Pts of timestamp _atom
  | Pind of index _atom

type constr = tatom bformula

let pts (o,t,t') = Pts (o,t,t')
let pind (o,i,i') = Pind (o,i,i')

let pp_tatom ppf = function
  | Pts (o,tl,tr) ->
    Fmt.pf ppf "@[<h>%a %a %a@]" pp_timestamp tl pp_ord o pp_timestamp tr
  | Pind (o,il,ir) ->
    Fmt.pf ppf "@[<h>%a %a %a@]" Index.pp il pp_ord o Index.pp ir

let not_tpred = function
  | Pts (o,t,t') -> pts (not_xpred (o,t,t'))
  | Pind (o,i,i') -> pind (not_xpred (o,i,i'))

let norm_tatom = function
  | Pts (o,t,t') -> norm_xatom (o,t,t') |> List.map pts
  | Pind _ as x -> [x]

let pp_constr ppf = pp_bformula pp_tatom ppf

(** Put a constraint in DNF using only atoms Eq, Neq and Leq *)
let constr_dnf (c : constr) =
  bf_dnf not_tpred c
  |> List.map (fun l -> List.map norm_tatom l
                        |> List.flatten)



(** Correspondence formulas *)

type fvar =
    TSVar of tvar
  | MessVar of mvar
  | IndexVar of index

let pp_fvar ppf = function
    TSVar t -> Tvar.pp ppf t
  | MessVar m -> Mvar.pp ppf m
  | IndexVar i -> Index.pp ppf i

let pp_typed_fvar ppf = function
    TSVar t -> Fmt.pf ppf "%a:timestamp" Tvar.pp t
  | MessVar m -> Fmt.pf ppf "%a:message" Mvar.pp m
  | IndexVar i -> Fmt.pf ppf "%a:index" Index.pp i

let make_fresh_of_type (v:fvar) =
    match v with
    | TSVar _ -> TSVar (Tvar.make_fresh ())
    | MessVar _ -> MessVar (Mvar.make_fresh ())
    | IndexVar _ -> IndexVar (Index.make_fresh ())
      
(** A formula is always of the form
  *   forall [uvars,uindices] such that [uconstr],
  *   [ufact] => [postcond],
  * with a postcondition that is a disjunction
  * of formulas of the form
  *   exists [evars,eindices] such that [econstr] and [efact]. *)
type formula = {
  uvars : fvar list;
(*  uvars : tvar list;
    uindices : indices; *)
  uconstr : constr;
  ufact : fact;
  postcond : postcond list
}
and postcond = {
  evars : fvar list;
(*  evars : tvar list;
    eindices : indices; *)
  econstr : constr;
  efact : fact
}

let get_tsvars (f:fvar list) =
  List.fold_left (fun acc t -> match t with TSVar t -> t::acc | _ -> acc) [] f

let get_messvars (f:fvar list) =
  List.fold_left (fun acc t -> match t with MessVar t -> t::acc | _ -> acc) [] f

let get_indexvars (f:fvar list) =
  List.fold_left (fun acc t -> match t with IndexVar t -> t::acc | _ -> acc) [] f


let pp_typed_fvars spref ppf vars =
  let open Fmt in
  let open Utils in
 let tsvars = get_tsvars vars in
  if tsvars <> [] then
    Fmt.pf ppf "@[<hv 2>%a@ (@[<hov>%a@] : %a)@]@;"
     (styled `Red (styled `Underline ident)) spref
     (Tvar.pp_list) tsvars
     (styled `Blue (styled `Bold ident)) "timestamp"
  else ();
  let indexvars = get_indexvars vars in
  if indexvars <> [] then
    Fmt.pf ppf "@[<hv 2>%a@ (@[<hov>%a@] : %a)@]@;"
      (styled `Red (styled `Underline ident)) spref
     Index.pp_list indexvars
     (styled `Blue (styled `Bold ident)) "index"
  else ();
  let messvars = get_messvars vars in
  if messvars <> [] then
    Fmt.pf ppf "@[<hv 2>%a@ (@[<hov>%a@] : %a)@]@;"
      (styled `Red (styled `Underline ident)) spref
     (Mvar.pp_list) messvars
     (styled `Blue (styled `Bold ident)) "message"
  else ()

let pp_q_vars s_q vars constr ppf () =
  let open Fmt in
  let open Utils in
  Fmt.pf ppf "%a" (pp_typed_fvars s_q) vars;
  if constr <> True then
    Fmt.pf ppf "@[<hv 2>%a@ @[<hov>%a@]@]@; "
      (styled `Red (styled `Underline ident)) "such that"
      pp_constr constr

let pp_postcond ppf f =
  Fmt.pf ppf "@[<v 0>%a%a@]"
    (pp_q_vars "exists" f.evars f.econstr) ()
    pp_fact f.efact

let pp_precond ppf f =
  Fmt.pf ppf "@[<v 0>%a%a@]"
    (pp_q_vars "forall" f.uvars f.uconstr) ()
    pp_fact f.ufact

let pp_formula ppf f =
  let open Fmt in
  let open Utils in
  match f.postcond with
  | [] -> pp_precond ppf f
  | [a] ->
      (* TODO refactor so that this prettier-printing
       * applies to multiple (or empty) postconditions *)
      if f.ufact = True then
        Fmt.pf ppf "@[<v 0>%a@;%a@]"
          (pp_q_vars "forall" f.uvars f.uconstr) ()
          pp_postcond a
      else
        Fmt.pf ppf "@[<v 0>%a@;%a %a@]"
          pp_precond f
          (styled `Red (styled `Underline ident)) "=>"
          pp_postcond a
  | a :: l ->
    Fmt.pf ppf "@[<v 0>%a@;%a %a%a@]"
      pp_precond f
      (styled `Red (styled `Underline ident)) "=>"
      pp_postcond a
      (list
         ~sep:(fun ppf () ->
             Fmt.pf ppf "%a "
             (styled `Red (styled `Underline ident)) "@;\\/")
         pp_postcond) l


(** Substitutions for all purpose, applicable to terms and timestamps alikes **)
(** substitutions are performed bottom to top to avoid loops **)

type asubst =
  | Term of term * term
  | TS of timestamp * timestamp
  | Index of index * index
             
type subst = asubst list

exception Substitution_error of string

let pp_asubst ppf e =
  let pp_el pp_t (t1,t2) = Fmt.pf ppf "%a->%a" pp_t t1 pp_t t2 in
  match e with
  | Term(t1,t2) -> pp_el pp_term (t1,t2)
  | TS(ts1,ts2) -> pp_el pp_timestamp (ts1,ts2)
  | Index(i1,i2) -> pp_el Index.pp (i1,i2)
                      

let pp_subst ppf s =
  Fmt.pf ppf "@[<hv 0>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf "@,") pp_asubst) s

     


let term_subst (s:subst) =
  List.fold_left (fun acc asubst -> match asubst with Term(t1,t2) -> (t1,t2)::acc | _ -> acc) [] s

let ts_subst (s:subst) =
  List.fold_left (fun acc asubst -> match asubst with TS(t1,t2) -> (t1,t2)::acc | _ -> acc) [] s

let to_isubst (s:subst) =
  List.fold_left (fun acc asubst -> match asubst with Index(t1,t2) -> (t1,t2)::acc | _ -> acc) [] s

let rec from_tvarsubst l =
  match l with
  | [] -> []
  | (tv1,tv2)::l -> (TS(TVar tv1,TVar tv2))::(from_tvarsubst l)

let rec from_isubst l =
  match l with
  | [] -> []
  | (i1,i2)::l -> (Index(i1,i2))::(from_isubst l)


let rec from_fvarsubst l =
  match l with
  | [] -> []
  | (TSVar t1,TSVar t2)::l ->
    (TS(TVar t1,TVar t2))::(from_fvarsubst l)
  | (MessVar t1,MessVar t2)::l ->
    (Term(MVar t1,MVar t2))::(from_fvarsubst l)
  | (IndexVar t1,IndexVar t2)::l ->
    (Index(t1,t2))::(from_fvarsubst l)
  | _ -> failwith "ill-typed substitution"
           
let get_term_subst (s:subst) (t:term) =
  try
    List.assoc t (term_subst s)
  with Not_found -> t

let get_ts_subst (s:subst) (ts:timestamp) =
  try
    List.assoc ts (ts_subst s)
  with Not_found -> ts

let get_index_subst (s:subst) (i:index) =
  try
    List.assoc i (to_isubst s)
  with Not_found -> i

let subst_index = get_index_subst
  
let rec subst_action (s:subst) (a:action) =
  match a with
  | [] -> []
  | a :: l ->
    let p, sis = a.par_choice in
    { par_choice = p, List.map (get_index_subst s) sis;
      sum_choice = a.sum_choice }
    :: subst_action s l

let subst_state (s:subst) ((st,is):state) =
  (st, List.map (get_index_subst s) is)

let rec subst_ts (s:subst) (ts:timestamp) =
  let newts = 
    (match ts with
     | TVar _ -> ts
     | TPred ts' -> TPred (subst_ts s ts')
     | TName (ac) -> TName (subst_action s ac)
    ) in
  get_ts_subst s newts

let rec subst_term (s:subst) (t:term) =
  let newt = (
    match t with
    | Fun (fs, lt) ->Fun (fs, List.map (subst_term s) lt) 
    | Name _ -> t
    | State (st, ts) -> State (subst_state s st, subst_ts s ts)
    | Macro (m,ts) -> Macro (m,subst_ts s ts)
    | MVar _ -> t
  ) in
  get_term_subst s newt


let subst_atom (s:subst) ((ord,a1,a2): atom) =
  (ord,subst_term s a1, subst_term s a2)

let rec subst_formula a_subst (s:subst) f =
  match f with
  | And (a,b) -> And (subst_formula a_subst s a, subst_formula a_subst s b )
  | Or (a,b) -> Or (subst_formula a_subst s a, subst_formula a_subst s b )
  | Impl (a,b) -> Impl (subst_formula a_subst s a, subst_formula a_subst s b )
  | Not a -> Not (subst_formula a_subst s a)
  | Atom at -> Atom (a_subst s at)
  | True | False -> f

let subst_fact = subst_formula subst_atom
    
let subst_tatom (s:subst) = function
  | Pts (ord, ts, ts') ->
    Pts (ord, subst_ts s ts, subst_ts s ts')
  | Pind (ord, i, i') ->  Pind(ord, get_index_subst s i,get_index_subst s i')

let subst_constr = subst_formula subst_tatom

(** Substitution in a post-condition.
    Pre-condition: [subst_postcond subst pc] require that [subst]
    co-domain is fresh in [pc]. *)
let subst_postcond subst pc =
  let subst = List.filter (function Index(v,_) -> not @@ List.mem v (get_indexvars pc.evars) | _ -> true) subst in
  let subst = List.filter (function TS(TVar v,_) -> not @@ List.mem v (get_tsvars pc.evars) | _ -> true ) subst in

  { pc with econstr = subst_constr subst pc.econstr;
            efact = subst_fact subst pc.efact }



(*
let ivar_subst_symb isubst (fn, is) = (fn, List.map (app_subst isubst) is)

let ivar_subst_state isubst (s : state) = ivar_subst_symb isubst s

let rec tvar_subst_ts tsubst ts = match ts with
  | TVar tv -> TVar (app_subst tsubst tv)
  | TPred ts' -> TPred (tvar_subst_ts tsubst ts')
  | TName _ -> ts

let rec ivar_subst_ts isubst = function
  | TVar _ as ts -> ts
  | TPred ts' -> TPred (ivar_subst_ts isubst ts')
  | TName a -> TName (ivar_subst_action isubst a)

let rec tvar_subst_term tsubst t = match t with
  | Fun (fs, lt) -> Fun (fs, List.map (tvar_subst_term tsubst) lt)
  | Name _ -> t
  | State (s, ts) -> State (s, tvar_subst_ts tsubst ts)
  | Macro (m,ts) -> Macro (m,tvar_subst_ts tsubst ts)
  | MVar _ -> t                    
  (* | Input ts -> Input (tvar_subst_ts tsubst ts) *)

let rec ivar_subst_term isubst t = match t with
  | Fun (fs, lt) -> Fun ( ivar_subst_symb isubst fs,
                          List.map (ivar_subst_term isubst) lt )
  | Name n -> Name (ivar_subst_symb isubst n)
  | State (s, ts) -> State ( ivar_subst_symb isubst s,
                             ivar_subst_ts isubst ts )
  | Macro (m,ts) -> Macro (m,ivar_subst_ts isubst ts)
  | MVar m -> m                    
  (* | Input ts -> Input (ivar_subst_ts isubst ts) *)

let subst_term isubst tsubst m = ivar_subst_term isubst m
                                 |> tvar_subst_term tsubst

let rec var_subst_form at_subst subst f = match f with
  | And (a,b) -> And ( var_subst_form at_subst subst a,
                       var_subst_form at_subst subst b )
  | Or (a,b) -> Or ( var_subst_form at_subst subst a,
                     var_subst_form at_subst subst b )
  | Impl (a,b) -> Impl ( var_subst_form at_subst subst a,
                         var_subst_form at_subst subst b )
  | Not a -> Not (var_subst_form at_subst subst a)
  | Atom at -> Atom (at_subst subst at)
  | True | False -> f

let tvar_subst_atom subst (ord,t,t') =
  (ord, tvar_subst_term subst t, tvar_subst_term subst t')

let ivar_subst_atom isubst (ord,t,t') =
  (ord, ivar_subst_term isubst t, ivar_subst_term isubst t')

let tvar_subst_fact = var_subst_form tvar_subst_atom

let ivar_subst_fact = var_subst_form ivar_subst_atom

let subst_fact isubst tsubst m = ivar_subst_fact isubst m
                                 |> tvar_subst_fact tsubst

let tvar_subst_tatom subst = function
  | Pts (ord, ts, ts') ->
    Pts (ord, tvar_subst_ts subst ts, tvar_subst_ts subst ts')
  | Pind _ as at -> at

let ivar_subst_tatom isubst = function
  | Pts (ord, ts, ts') ->
    Pts (ord, ivar_subst_ts isubst ts, ivar_subst_ts isubst ts')
  | Pind (ord, i, i') -> Pind (ord, app_subst isubst i, app_subst isubst i')

let tvar_subst_constr = var_subst_form tvar_subst_tatom

let ivar_subst_constr = var_subst_form ivar_subst_tatom

let subst_constr isubst tsubst m = ivar_subst_constr isubst m
                                   |> tvar_subst_constr tsubst


(** Timestamp variables substitution in a post-condition.
    Pre-condition: [tvar_subst_postcond subst pc] require that [subst]
    co-domain is fresh in [pc]. *)
let tvar_subst_postcond subst pc =
  let subst = List.filter (fun (v,_) -> not @@ List.mem v pc.evars) subst in
  { pc with econstr = tvar_subst_constr subst pc.econstr;
            efact = tvar_subst_fact subst pc.efact }

(** Index variables substitution in a post-condition.
    Pre-condition: [ivar_subst_postcond isubst pc] require that [isubst]
    co-domain is fresh in [pc]. *)
let ivar_subst_postcond subst pc =
  let subst = List.filter (fun (v,_) -> not @@ List.mem v pc.eindices) subst in
  { pc with econstr = ivar_subst_constr subst pc.econstr;
            efact = ivar_subst_fact subst pc.efact }

(** Substitution in a post-condition.
    Pre-condition: [subst_postcond isubst tsubst pc] require that [isubst]
    and [tsubst] co-domains are fresh in [pc]. *)
let subst_postcond isubst tsubst m = ivar_subst_postcond isubst m
                                     |> tvar_subst_postcond tsubst
*)
let svars (tvs,ivs) (_, is) =
  (tvs, is @ ivs)

let rec tsvars (tvs,ivs) = function
  | TVar tv -> (tv :: tvs, ivs)
  | TName a -> (tvs, action_indices a @ ivs)
  | TPred ts -> tsvars (tvs,ivs) ts

let rec tvars acc = function
  | Fun (fs, lt) -> List.fold_left tvars (svars acc fs) lt
  | Name n -> svars acc n
  | State (s, ts) -> tsvars (svars acc s) ts
  (* | Input ts *)
  | Macro (_,ts) -> tsvars acc ts
  | MVar _ ->  ([],[])

(** [term_vars t] returns the timestamp and index variables of [t]*)
let term_vars t =
  let tvs, ivs = tvars ([],[]) t in
  ( List.sort_uniq Pervasives.compare tvs,
    List.sort_uniq Pervasives.compare ivs )

(** [tss_vars tss] returns the timestamp and index variables of [tss]*)
let tss_vars tss =
  let tvs, ivs = List.fold_left tsvars ([],[]) tss in
  ( List.sort_uniq Pervasives.compare tvs,
    List.sort_uniq Pervasives.compare ivs )


let rec tts acc = function
  | Fun (fs, lt) -> List.fold_left tts acc lt
  | Name n -> acc
  | State (_, ts)
  (* | Input ts *)
  | Macro (_,ts) -> ts :: acc
  | MVar _ -> []
              
(** [term_ts t] returns the timestamps appearing in [t] *)
let term_ts t = tts [] t |> List.sort_uniq Pervasives.compare

let rec atsts acc = function
  | [] -> acc
  | (_,t,t') :: l -> atsts (tts (tts acc t) t') l

(** [atoms_ts ats] returns the timestamps appearing in [ats] *)
let atoms_ts at = atsts [] at |> List.sort_uniq Pervasives.compare

let rec tatsts acc = function
  | [] -> acc
  | (Pind _) :: l -> tatsts acc l
  | (Pts (_,ts,ts')) :: l -> tatsts (ts :: ts' :: acc) l

let f_fts f_at acc fact =
  let rec fts acc = function
  | True | False -> acc
  | And (a,b) | Or (a,b) | Impl (a,b) -> fts (fts acc a) b
  | Not a -> fts acc a
  | Atom at -> f_at acc at in

  fts acc fact

(** [fact_ts f] returns the timestamps appearing in [f] *)
let fact_ts f = f_fts (fun acc x -> atsts acc [x]) [] f

(** [constr_ts c] returns the timestamps appearing in [c] *)
let constr_ts c = f_fts (fun acc x -> tatsts acc [x]) [] c
