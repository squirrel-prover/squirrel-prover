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
