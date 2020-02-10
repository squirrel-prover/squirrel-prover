open Atom
open Term
(** First order formulas *)

type formula = Term.formula


let rec pp_foformula pp_atom pp_var_list ppf = function
  | ForAll (vs, b) ->
    Fmt.pf ppf "@[forall (@[%a@]),@ %a@]"
      pp_var_list vs (pp_foformula pp_atom pp_var_list) b
  | Exists (vs, b) ->
    Fmt.pf ppf "@[exists (@[%a@]),@ %a@]"
      pp_var_list vs (pp_foformula pp_atom pp_var_list) b
  | And (bl, br) ->
    Fmt.pf ppf "@[<1>(%a@ &&@ %a)@]"
      (pp_foformula pp_atom pp_var_list) bl
      (pp_foformula pp_atom pp_var_list) br
  | Or (bl, br) ->
    Fmt.pf ppf "@[<1>(%a@ ||@ %a)@]"
      (pp_foformula pp_atom pp_var_list) bl
      (pp_foformula pp_atom pp_var_list) br
  | Impl (bl, br) ->
    Fmt.pf ppf "@[<1>(%a@ =>@ %a)@]"
      (pp_foformula pp_atom pp_var_list) bl
      (pp_foformula pp_atom pp_var_list) br
  | Not b ->
    Fmt.pf ppf "not(@[%a@])" (pp_foformula pp_atom pp_var_list) b
  | Atom a -> pp_atom ppf a
  | True -> Fmt.pf ppf "True"
  | False -> Fmt.pf ppf "False"

let pp_formula = pp_foformula pp_generic_atom Vars.pp_typed_list
let pp = pp_formula

let rec subst_foformula a_subst (s : Term.subst) (f) =
  match f with
  | ForAll (vs,b) -> ForAll (vs, subst_foformula a_subst s b)
  | Exists (vs,b) -> Exists (vs, subst_foformula a_subst s b)
  | And (a, b) ->
    And (subst_foformula a_subst s a, subst_foformula a_subst s b )
  | Or (a, b) ->
    Or (subst_foformula a_subst s a, subst_foformula a_subst s b )
  | Impl (a, b) ->
    Impl (subst_foformula a_subst s a, subst_foformula a_subst s b )
  | Not a -> Not (subst_foformula a_subst s a)
  | Atom at -> Atom (a_subst s at)
  | True | False -> f

let subst_formula : Term.subst -> formula -> formula =
  subst_foformula subst_generic_atom

exception Not_a_disjunction

let rec disjunction_to_atom_list = function
  | False -> []
  | Atom at -> [at]
  | Or (a, b) -> disjunction_to_atom_list a @ disjunction_to_atom_list b
  | _ -> raise Not_a_disjunction
