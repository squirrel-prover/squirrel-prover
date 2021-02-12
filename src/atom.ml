(** Atoms *)

type ord = Term.ord
type ord_eq = Term.ord_eq

type ('a,'b) _atom  = ('a,'b) Term._atom

type generic_atom = Term.generic_atom

type message_atom = [ `Message of ord_eq * Term.message
                               * Term.message ]

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

let pp_message_atom ppf (`Message (o,tl,tr)) =
  Fmt.pf ppf "@[%a@ %a@ %a@]" Term.pp tl pp_ord o Term.pp tr

(** Negate the atom *)
let not_xpred (o,l,r) = (not_ord o, l, r)
let not_xpred_eq (o,l,r) = (not_ord_eq o, l, r)

let not_message_atom = function
  | `Message t -> `Message (not_xpred_eq t)
(** Replace an atom by an equivalent list of atoms using only Eq,Neq and Leq *)
let norm_xatom (o, l, r) =
  match o with
  | `Eq | `Neq | `Leq -> [(o, l, r)]
  | `Geq -> [(`Leq, r, l)]
  | `Lt -> (`Leq, l, r) :: [(`Neq, l, r)]
  | `Gt -> (`Leq, r, l) :: [(`Neq, r, l)]

(** Precondition : must only be called on Eq | Leq | Neq atoms *)
let add_xeq od xeq (eqs, leqs, neqs) =
  match od with
  | `Eq -> (xeq :: eqs, leqs, neqs)
  | `Leq -> (eqs, xeq :: leqs, neqs)
  | `Neq -> (eqs, leqs, xeq :: neqs)
  | _ -> assert false

type trace_atom = [
  | `Timestamp of (ord,Term.timestamp) _atom
  | `Index of (ord_eq,Vars.index) _atom
]

let not_trace_atom : trace_atom -> trace_atom = function
  | `Timestamp (o,t,t') -> `Timestamp (not_xpred (o,t,t'))
  | `Index (o,i,i') -> `Index (not_xpred_eq (o,i,i'))


let subst_message_atom (s : Term.subst) (`Message (ord, a1, a2)) =
  `Message (ord, Term.subst s a1, Term.subst s a2)

let subst_trace_atom (s:Term.subst) = function
  | `Timestamp (ord, ts, ts') ->
    `Timestamp (ord, Term.subst s ts, Term.subst s ts')
  | `Index (ord, i, i') ->
    `Index(ord, Term.subst_var s i,Term.subst_var s i')

let subst_generic_atom s = function
  | `Happens a -> `Happens (Term.subst s a)
  | #message_atom as a -> (subst_message_atom s a :> generic_atom)
  | #trace_atom as a -> (subst_trace_atom s a :> generic_atom)

let pp_trace_atom ppf : trace_atom -> unit = function
  | `Timestamp (o,tl,tr) ->
    Fmt.pf ppf "@[<hv>%a@ %a@ %a@]" Term.pp tl pp_ord o Term.pp tr
  | `Index (o,il,ir) ->
    Fmt.pf ppf "@[<hv>%a@ %a@ %a@]" Vars.pp il pp_ord o Vars.pp ir

let pp_generic_atom ppf = function
  | `Happens a -> Fmt.pf ppf "happens(%a)" Term.pp a
  | #message_atom as a -> pp_message_atom ppf a
  | #trace_atom as a -> pp_trace_atom ppf a

let rec tatsts acc = function
  | [] -> acc
  | (`Index _) :: l -> tatsts acc l
  | (`Timestamp (_, ts, ts')) :: l -> tatsts (ts :: ts' :: acc) l

let trace_atoms_ts at = tatsts [] at |> List.sort_uniq Stdlib.compare

let rec tatsind acc = function
  | [] -> acc
  | (`Index (_,i,j)) :: l -> tatsind (i :: j :: acc) l
  | (`Timestamp (_, ts, ts')) :: l -> tatsind acc l

let trace_atoms_ind at = tatsind [] at |> List.sort_uniq Stdlib.compare
