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

(** Finite set of action identifiers *)
type action = Action of string

let pp_action ppf = function Action s -> Fmt.pf ppf "%s" s

(** Timestamps represent positions in a trace *)

type tvar = Tvar_i of int

let pp_tvar ppf = function Tvar_i i -> Fmt.pf ppf "ts%d" i

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

type name

type nsymb = name * indices

(** Function symbols are built from a name (from a finite set)
  * and a list of indices.
  *
  * TODO must include builtins such as if-then-else, equality, successor...
  *)

type fname

type fsymb = fname * indices

(** Memory cells are represented by state variable, themselves
  * derived from a name (from a finite set) and indices.
  *
  * TODO simplify design to merge name, function and state names ?
  *)

type sname

type state = sname * indices

(** Terms *)
type term =
  | Fun of fsymb * term list
  | Name of nsymb
  | State of state * timestamp
  | Output of timestamp
  | Input of timestamp

(** Boolean formulas *)
type 'a bformula =
  | And of 'a bformula * 'a bformula
  | Or of 'a bformula * 'a bformula
  | Not of 'a bformula
  | Impl of 'a bformula * 'a bformula
  | Atom of 'a

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

(** [bf_dnf nlit b] puts the  bformula [b] in DNF, using [nlit] to transform
    negative atoms into positive atoms *)
let bf_dnf : ('a -> 'a) -> 'a bformula -> 'a list list = fun nlit b ->
  let rec simp flip = function
    | Atom a -> if flip then Atom (nlit a) else Atom a
    | Or (l,r) -> Or (simp flip l, simp flip r)
    | And (l,r) -> And (simp flip l, simp flip r)
    | Impl (l,r) ->  Or (Not l, r) |> simp flip
    | Not b -> simp (not flip) b in

  let rec dnf = function
    | Or (a,b) -> dnf a @ dnf b
    | Atom a -> [[a]]
    | And (a,b) ->
      let bdnf = dnf b in
      List.fold_left (fun acc c ->
          (List.fold_left (fun acc c' ->
               (c @ c') :: acc) acc bdnf))
        [] (dnf a)
    | Impl _ | Not _ -> assert false in

  simp false b |> dnf


(** Predicates *)

type ord = Eq | Neq | Leq | Geq | Lt | Gt
type predicate = ord * term * term

type fact = predicate bformula

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

(** Negate the predicate *)
let not_xpred (o,l,r) = (not_ord o, l, r)

(** Replace a predicate by an equivalent list of predicates using
    only Eq,Neq,Leq *)
let norm_xpredicate (o,l,r) = match o with
  | Eq | Neq | Leq -> [(o,l,r)]
  | Geq -> [(Leq,r,l)]
  | Lt -> (Leq,l,r) :: [(Neq,l,r)]
  | Gt -> (Leq,r,l) :: [(Neq,r,l)]


(** Constraints *)

type tpredicate = ord * timestamp * timestamp
type constr = tpredicate bformula

let pp_tpredicate ppf (o,tl,tr) =
  Fmt.pf ppf "@[<h>%a%a%a@]" pp_timestamp tl pp_ord o  pp_timestamp tr

let pp_constr ppf = pp_bformula pp_tpredicate ppf

let constr_dnf c = bf_dnf not_xpred c
                   |> List.map (fun l -> List.map norm_xpredicate l
                                         |> List.flatten)

(** Correspondence formulas *)


(** A formula is always of the form
  *   forall [uvars] such that [uconstr],
  *   [ufact] => [postcond],
  * with a postcondition that is a disjunction
  * of formulas of the form
  *   exists [evars] such that [econstr] and [efact]. *)
type formula = {
  uvars : tvar list;
  uconstr : constr;
  ufact : fact;
  postcond : postcond list
}
and postcond = {
  evars : tvar list;
  econstr : constr;
  efact : fact
}
