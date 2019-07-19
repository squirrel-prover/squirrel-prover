(** Terms and formulas for the Meta-BC logic.
  *
  * This modules describes the syntax of the logic. It does not
  * provide low-level representations, normal forms, etc. that
  * are to be used in automated reasoning, nor does it provide
  * representations necessary for the front-end involving
  * processes, axioms, etc. *)

(** Indices are used to generate arbitrary families of terms *)
type index = Index of int
type indices = index list

let pp_index ppf = function Index i -> Fmt.pf ppf "i%d" i

let pp_indices ppf l =
  Fmt.pf ppf "@[<hov>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@,") pp_index) l

let idx_cpt = ref 0
let fresh_index () = incr idx_cpt; Index (!idx_cpt - 1)

(** Finite set of action identifiers *)
type action = Action of string

let mk_action s = Action s

let pp_action ppf = function Action s -> Fmt.pf ppf "%s" s

(** Timestamps represent positions in a trace *)

type tvar = Tvar_i of int

let pp_tvar ppf = function Tvar_i i -> Fmt.pf ppf "ts%d" i

let tvar_cpt = ref 0
let fresh_tvar () = incr tvar_cpt; Tvar_i (!tvar_cpt - 1)

type timestamp =
  | TVar of tvar
  | TPred of timestamp
  | TName of action * indices

let rec pp_timestamp ppf = function
  | TVar tv -> pp_tvar ppf tv
  | TPred ts -> Fmt.pf ppf "@[<hov>p(%a)@]" pp_timestamp ts
  | TName (a,is) -> Fmt.pf ppf "@[%a[%a]@]" pp_action a pp_indices is

(** Names represent random values, uniformly sampled by the process.
  * A name symbol is derived from a name (from a finite set) and
  * a list of indices. *)

type name = Name of string

let pp_name ppf = function Name s -> Fmt.pf ppf "n!%s" s

type nsymb = name * indices

let pp_nsymb ppf (n,is) = Fmt.pf ppf "%a(%a)" pp_name n pp_indices is

(** Function symbols are built from a name (from a finite set)
  * and a list of indices.
  *
  * TODO must include builtins such as if-then-else, equality, successor, xor ...
  * Adrien: already added some
  * Some keywords should probably be forbidden, e.g. "in", "out"
  *)

type fname = Fname of string

let pp_fname ppf = function Fname s -> Fmt.pf ppf "%s" s

type fsymb = fname * indices

let pp_fsymb ppf (fn,is) = match is with
  | [] -> Fmt.pf ppf "%a" pp_fname fn
  | _ -> Fmt.pf ppf "%a[%a]" pp_fname fn pp_indices is

let mk_fname f = (Fname f, [])

(** Boolean function symbols *)
let f_false = (Fname "false", [])
let f_true = (Fname "true", [])
let f_and = (Fname "and", [])
let f_or = (Fname "or", [])

(** IfThenElse function symbol *)
let f_ite = (Fname "ite", [])

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

let pp_sname ppf = function Sname s -> Fmt.pf ppf "s!%s" s

type state = sname * indices

let pp_state ppf (sn,is) = Fmt.pf ppf "%a(%a)" pp_sname sn pp_indices is

(** Terms *)
type term =
  | Fun of fsymb * term list
  | Name of nsymb
  | State of state * timestamp
  | Output of timestamp
  | Input of timestamp

type t = term

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


(** [bf_dnf nlit b] puts the  bformula [b] in DNF, using [nlit] to transform
    negative atoms into positive atoms *)
let bf_dnf : ('a -> 'a) -> 'a bformula -> 'a list list = fun nlit b ->
  let rec simp flip = function
    | Atom a -> if flip then Atom (nlit a) else Atom a
    | True -> if flip then False else True
    | False -> if flip then True else False
    | Or (l,r) -> Or (simp flip l, simp flip r)
    | And (l,r) -> And (simp flip l, simp flip r)
    | Impl (l,r) ->  Or (Not l, r) |> simp flip
    | Not b -> simp (not flip) b in

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

  simp false b |> dnf


(** Atoms *)

type ord = Eq | Neq | Leq | Geq | Lt | Gt
type atom = ord * term * term

type fact = atom bformula

let pp_ord ppf = function
  | Eq -> Fmt.pf ppf "Eq"
  | Neq -> Fmt.pf ppf "Neq"
  | Leq -> Fmt.pf ppf "Leq"
  | Geq -> Fmt.pf ppf "Geq"
  | Lt -> Fmt.pf ppf "Lt"
  | Gt -> Fmt.pf ppf "Gt"

let not_ord o = match o with
  | Eq -> Neq
  | Neq -> Eq
  | Leq -> Gt
  | Geq -> Lt
  | Lt -> Geq
  | Gt -> Leq

(** Negate the atom *)
let not_xpred (o,l,r) = (not_ord o, l, r)

(** Replace an atom by an equivalent list of atoms using
    only Eq,Neq and Leq *)
let norm_xatom (o,l,r) = match o with
  | Eq | Neq | Leq -> [(o,l,r)]
  | Geq -> [(Leq,r,l)]
  | Lt -> (Leq,l,r) :: [(Neq,l,r)]
  | Gt -> (Leq,r,l) :: [(Neq,r,l)]


(** Constraints:
    - [Pind (o,i,i')] : [o] must be either [Eq] or [Neq] *)
type tatom =
  | Pts of ord * timestamp * timestamp
  | Pind of ord * index * index

type constr = tatom bformula

let pts (o,t,t') = Pts (o,t,t')
let pind (o,i,i') = Pind (o,i,i')

let pp_tatom ppf = function
  | Pts (o,tl,tr) ->
    Fmt.pf ppf "@[<h>%a%a%a@]" pp_timestamp tl pp_ord o pp_timestamp tr
  | Pind (o,il,ir) ->
    Fmt.pf ppf "@[<h>%a%a%a@]" pp_index il pp_ord o pp_index ir

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


(** A formula is always of the form
  *   forall [uvars,uindices] such that [uconstr],
  *   [ufact] => [postcond],
  * with a postcondition that is a disjunction
  * of formulas of the form
  *   exists [evars,eindices] such that [econstr] and [efact]. *)
type formula = {
  uvars : tvar list;
  uindices : indices;
  uconstr : constr;
  ufact : fact;
  postcond : postcond list
}
and postcond = {
  evars : tvar list;
  eindices : indices;
  econstr : constr;
  efact : fact
}


let app_subst subst x = try List.assoc x subst with Not_found -> x

let ivar_subst_symb isubst (fn, is) = (fn, List.map (app_subst isubst) is)

let rec tvar_subst_ts tsubst ts = match ts with
  | TVar tv -> TVar (app_subst tsubst tv)
  | TPred ts' -> TPred (tvar_subst_ts tsubst ts')
  | TName _ -> ts

let rec ivar_subst_ts isubst = function
  | TVar _ as ts -> ts
  | TPred ts' -> TPred (ivar_subst_ts isubst ts')
  | TName (n,is) -> TName (n,  List.map (app_subst isubst) is)

(** Timestamp variables substitution in a term*)
let rec tvar_subst_term tsubst t = match t with
  | Fun (fs, lt) -> Fun (fs, List.map (tvar_subst_term tsubst) lt)
  | Name _ -> t
  | State (s, ts) -> State (s, tvar_subst_ts tsubst ts)
  | Output ts -> Output (tvar_subst_ts tsubst ts)
  | Input ts -> Input (tvar_subst_ts tsubst ts)

(** Index variables substitution in a term *)
let rec ivar_subst_term isubst t = match t with
  | Fun (fs, lt) -> Fun ( ivar_subst_symb isubst fs,
                          List.map (ivar_subst_term isubst) lt )
  | Name n -> Name (ivar_subst_symb isubst n)
  | State (s, ts) -> State ( ivar_subst_symb isubst s,
                             ivar_subst_ts isubst ts )
  | Output ts -> Output (ivar_subst_ts isubst ts)
  | Input ts -> Input (ivar_subst_ts isubst ts)

(** Variables substitution in a formula *)
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

(** Timestamp variables substitution in a fact *)
let tvar_subst_fact = var_subst_form tvar_subst_atom

(** Index variables substitution in a fact *)
let ivar_subst_fact = var_subst_form ivar_subst_atom

let tvar_subst_tatom subst = function
  | Pts (ord, ts, ts') ->
    Pts (ord, tvar_subst_ts subst ts, tvar_subst_ts subst ts')
  | Pind _ as at -> at

let ivar_subst_tatom isubst = function
  | Pts (ord, ts, ts') ->
    Pts (ord, ivar_subst_ts isubst ts, ivar_subst_ts isubst ts')
  | Pind (ord, i, i') -> Pind (ord, app_subst isubst i, app_subst isubst i')

(** Timestamp variables substitution in a constraint *)
let tvar_subst_constr = var_subst_form tvar_subst_tatom

(** Index variables substitution in a constraint *)
let ivar_subst_constr = var_subst_form ivar_subst_tatom

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


let svars (tvs,ivs) (_, is) =
  (tvs, List.sort_uniq Pervasives.compare (is @ ivs))

let rec tsvars (tvs,ivs) = function
  | TVar tv -> (List.sort_uniq Pervasives.compare (tv :: tvs), ivs)
  | TName (_, is) -> (tvs, List.sort_uniq Pervasives.compare (is @ ivs))
  | TPred ts -> tsvars (tvs,ivs) ts

let rec tvars acc = function
  | Fun (fs, lt) -> List.fold_left tvars (svars acc fs) lt
  | Name n -> svars acc n
  | State (s, ts) -> tsvars (svars acc s) ts
  | Input ts | Output ts -> tsvars acc ts

(** [term_vars t] returns the timestamp and index variables of [t]*)
let term_vars t = tvars ([],[]) t

(** [tss_vars tss] returns the timestamp and index variables of [tss]*)
let tss_vars tss = List.fold_left tsvars ([],[]) tss
