(** Atoms *)

type ord = [ `Eq | `Neq | `Leq | `Geq | `Lt | `Gt ]
type ord_eq = [ `Eq | `Neq ]

type ('a,'b) _atom = 'a * 'b * 'b

(* TODO : rename to message *)
type term_atom = [ `Message of (ord_eq,Term.message) _atom ]

let atom_vars avars (`Message (o,a1,a2)) =
  (avars a1 @ avars a1)
  |> List.sort_uniq Pervasives.compare

let term_atom_vars = atom_vars Term.get_vars

let pp_ord ppf = function
  | `Eq -> Fmt.pf ppf "="
  | `Neq -> Fmt.pf ppf "<>"
  | `Leq -> Fmt.pf ppf "<="
  | `Geq -> Fmt.pf ppf ">="
  | `Lt -> Fmt.pf ppf "<"
  | `Gt -> Fmt.pf ppf ">"

let not_ord o = match o with
  | `Eq -> `Neq
  | `Neq -> `Eq
  | `Leq -> `Gt
  | `Geq -> `Lt
  | `Lt -> `Geq
  | `Gt -> `Leq
let not_ord_eq : ord_eq -> ord_eq = function
  | `Eq -> `Neq
  | `Neq -> `Eq

let pp_term_atom ppf (`Message (o,tl,tr)) =
  Fmt.pf ppf "@[%a@ %a@ %a@]" Term.pp tl pp_ord o Term.pp tr

(** Negate the atom *)
let not_xpred (o,l,r) = (not_ord o, l, r)
let not_xpred_eq (o,l,r) = (not_ord_eq o, l, r)

(** Replace an atom by an equivalent list of atoms using only Eq,Neq and Leq *)
let norm_xatom (o, l, r) =
  match o with
  | `Eq | `Neq | `Leq -> [(o, l, r)]
  | `Geq -> [(`Leq, r, l)]
  | `Lt -> (`Leq, l, r) :: [(`Neq, l, r)]
  | `Gt -> (`Leq, r, l) :: [(`Neq, r, l)]

let add_xeq od xeq (eqs, leqs, neqs) =
  match od with
  | `Eq -> (xeq :: eqs, leqs, neqs)
  | `Leq -> (eqs, xeq :: leqs, neqs)
  | `Neq -> (eqs, leqs, xeq :: neqs)
  | _ -> raise (Failure ("add_xeq: bad comparison operator"))

let add_xeq_eq od xeq (eqs, neqs) =
  match od with
  | `Eq -> (xeq :: eqs, neqs)
  | `Neq -> (eqs, xeq :: neqs)
(* TODO rename to trace *)
type trace_atom = [
  | `Timestamp of (ord,Term.timestamp) _atom
  | `Index of (ord_eq,Index.t) _atom
]

type generic_atom = [
  | `Message of (ord_eq,Term.message) _atom
  | `Timestamp of (ord,Term.timestamp) _atom
  | `Index of (ord_eq,Index.t) _atom
  | `Happens of Term.timestamp
]

let subst_term_atom (s : Term.subst) (`Message (ord, a1, a2)) =
  `Message (ord, Term.subst s a1, Term.subst s a2)

let subst_trace_atom (s:Term.subst) = function
  | `Timestamp (ord, ts, ts') ->
    `Timestamp (ord, Term.subst s ts, Term.subst s ts')
  | `Index (ord, i, i') ->
    `Index(ord, Term.subst_index s i,Term.subst_index s i')

let subst_generic_atom s = function
  | `Happens a -> `Happens (Term.subst s a)
  | #term_atom as a -> (subst_term_atom s a :> generic_atom)
  | #trace_atom as a -> (subst_trace_atom s a :> generic_atom)

let pp_trace_atom ppf : trace_atom -> unit = function
  | `Timestamp (o,tl,tr) ->
    Fmt.pf ppf "@[<hv>%a@ %a@ %a@]" Term.pp tl pp_ord o Term.pp tr
  | `Index (o,il,ir) ->
    Fmt.pf ppf "@[<hv>%a@ %a@ %a@]" Vars.pp il pp_ord o Vars.pp ir

let pp_generic_atom ppf = function
  | `Happens a -> Fmt.pf ppf "happens(%a)" Term.pp a
  | #term_atom as a -> pp_term_atom ppf a
  | #trace_atom as a -> pp_trace_atom ppf a

let trace_atom_vars = function
  | `Timestamp (_,ts,ts') -> Term.get_vars ts @ Term.get_vars ts'
  | `Index (o,i,i') -> [Vars.EVar i;Vars.EVar i']

let generic_atom_var = function
  | #trace_atom as a -> trace_atom_vars a
  | #term_atom as a -> term_atom_vars a
  | `Happens a -> Term.get_vars a

let rec atsts acc = function
  | [] -> acc
  | `Message (_, t, t') :: l -> atsts (Term.get_ts t @ Term.get_ts t' @ acc) l

let term_atoms_ts at = atsts [] at |> List.sort_uniq Pervasives.compare

let rec tatsts acc = function
  | [] -> acc
  | (`Index _) :: l -> tatsts acc l
  | (`Timestamp (_, ts, ts')) :: l -> tatsts (ts :: ts' :: acc) l
