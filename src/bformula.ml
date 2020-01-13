open Term
open Atom

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
  | And (bl, br) ->
    Fmt.pf ppf "@[<hv>(%a && %a)@]"
      (pp_bformula pp_atom) bl (pp_bformula pp_atom) br
  | Or (bl, br) ->
    Fmt.pf ppf "@[<hv>(%a || %a)@]"
      (pp_bformula pp_atom) bl (pp_bformula pp_atom) br
  | Impl (bl, br) ->
    Fmt.pf ppf "@[<hv>(%a -> %a)@]"
      (pp_bformula pp_atom) bl (pp_bformula pp_atom) br
  | Not b ->
    Fmt.pf ppf "@[<hv>not(%a)@]" (pp_bformula pp_atom) b
  | Atom a -> pp_atom ppf a
  | True -> Fmt.pf ppf "true"
  | False -> Fmt.pf ppf "false"

let atoms b =
  let rec aux acc = function
    | True | False -> acc
    | And (a, b) | Or (a, b) | Impl (a, b) -> aux (aux acc a) b
    | Not a -> aux acc a
    | Atom at -> at :: acc in
  aux [] b

(** Evaluate trivial subformula. *)
let rec triv_eval = function
  | Or (a, b) ->
    begin
      match triv_eval a, triv_eval b with
      | _, True | True,_ -> True
      | _ as te, False | False, (_ as te) -> te
      | _ as ta, (_ as tb) -> Or (ta, tb)
    end

  | And (a, b) ->
    begin
      match triv_eval a, triv_eval b with
      | _ as te, True | True, (_ as te) -> te
      | _, False | False,_ -> False
      | _ as ta, (_ as tb) -> And (ta, tb)
    end

  | Impl (a, b) ->
    begin
      match triv_eval a, triv_eval b with
      | _, True | False, _ -> True
      | True, (_ as te) -> te
      | _ as ta, (_ as tb) -> Impl (ta, tb)
    end

  | Not a ->
    begin
      match triv_eval a with
      | True -> False
      | False -> True
      | _ as ta -> Not ta
    end

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


type fact = term_atom bformula

let pp_fact = pp_bformula pp_term_atom
type trace_formula = trace_atom bformula

let pts (o, t, t') = `Timestamp (o, t, t')

let not_tpred : trace_atom -> trace_atom = function
  | `Timestamp (o,t,t') -> `Timestamp (not_xpred (o,t,t'))
  | `Index (o,i,i') -> `Index (not_xpred_eq (o,i,i'))

let norm_tatom = function
  | `Timestamp (o,t,t') -> norm_xatom (o,t,t') |> List.map pts
  | `Index _ as x -> [x]

let not_trace_atom a =  (not_tpred a)

let pp_trace_formula ppf = pp_bformula pp_trace_atom ppf

let trace_formula_dnf (c : trace_formula) =
  bf_dnf not_tpred c
  |> List.map (fun l -> List.map norm_tatom l
                        |> List.flatten)

let rec subst_bformula a_subst (s : subst) (f) =
  match f with
  | And (a, b) -> And (subst_bformula a_subst s a, subst_bformula a_subst s b )
  | Or (a, b) -> Or (subst_bformula a_subst s a, subst_bformula a_subst s b )
  | Impl (a, b) ->
    Impl (subst_bformula a_subst s a, subst_bformula a_subst s b )
  | Not a -> Not (subst_bformula a_subst s a)
  | Atom at -> Atom (a_subst s at)
  | True | False -> f

let subst_fact = subst_bformula subst_term_atom

let subst_trace_formula = subst_bformula subst_trace_atom

let f_fts f_at acc fact =
  let rec fts acc = function
    | True | False -> acc
    | And (a, b) | Or (a, b) | Impl (a, b) -> fts (fts acc a) b
    | Not a -> fts acc a
    | Atom at -> f_at acc at in

  fts acc fact

let fact_ts f = f_fts (fun acc x -> atsts acc [x]) [] f

let trace_formula_ts c = f_fts (fun acc x -> tatsts acc [x]) [] c
