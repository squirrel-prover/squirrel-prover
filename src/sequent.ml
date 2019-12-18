open Utils
open Action
open Term
open Bformula
open Formula

(* The generic type for hypothesis, with arbtitry type of formulas and tag. *)
type ('a, 'b) hypothesis = {
  name_prefix : string;
  name_suffix : int;
  hypothesis : 'b;
  tag :  'a ;
  visible : bool;
}

let name hypo =
  if hypo.name_suffix <> 0 then
    Fmt.strf "%s%i" hypo.name_prefix hypo.name_suffix
  else
    Fmt.strf "%s" hypo.name_prefix

exception Non_existing_hypothesis

module M = Map.Make(String)


(* An set of hypothesis is made of two map. One maps hypothesis names
   (accordingly to [name]) to variables, and the second maps
   name prefixes to the current biggest name_suffix for this
   name_prefix. *)
type ('a, 'b) hypotheses = ((('a, 'b) hypothesis ) M.t * int M.t)

let empty_hypotheses =  (M.empty,M.empty)

let select_and_update (e1,e2) name update =
  try
    let hypo = M.find name e1 in
    (hypo, (M.add name (update hypo) e1,e2))
  with Not_found -> raise Non_existing_hypothesis

let add_hypothesis visible tag hypo name_prefix (e1,e2) : ('a, 'b) hypotheses =
  let name_suffix =
    try
      (M.find name_prefix e2) + 1
    with Not_found -> 0
  in
  let v = { name_prefix = name_prefix;
            name_suffix = name_suffix;
            hypothesis = hypo;
            tag = tag;
            visible = visible;
          }
  in
  (M.add (name v) v e1, M.add name_prefix name_suffix e2)

let hypotheses_to_list (e1,e2) =
  let r1,r2 = M.bindings e1 |> List.split in
  r2

let mem_hypotheses f hs =
  hypotheses_to_list hs
  |> List.exists (fun hypo -> hypo.hypothesis = f)

let pp_hypothesis pp_formula ppf hypo =
  Fmt.pf ppf "%s: %a" (name hypo) pp_formula hypo.hypothesis

let pp_hypotheses pp_formula ppf hs =
  Fmt.pf ppf "@[<hov>%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@") (pp_hypothesis pp_formula))
    (List.filter (fun h -> h.visible) (hypotheses_to_list hs))

type mess_tag = { t_euf : bool}

type trace_tag = unit

type formula_tag = unit

type message_hypothesis = (mess_tag, term_atom) hypothesis

type message_hypotheses = (mess_tag, term_atom) hypotheses
type trace_hypotheses = (trace_tag, trace_formula) hypotheses
type formula_hypotheses = (formula_tag, formula) hypotheses

let set_euf b h =
  {h with tag = {t_euf =b}}

type sequent = {
  env : Vars.env;
  happens_hypotheses : action list;
  message_hypotheses : message_hypotheses;
  trace_hypotheses :  trace_hypotheses;
  formula_hypotheses : formula_hypotheses;
  formula : formula;
  (* trs is either None, or the current term rewritting system corresponding to
     the message hypotheses. Must be se to None if the message hypotheses set
     changes. *)
  trs : Completion.state option;
  (* models is either None, or the current models corresponding to the trace
     hypotheses. Must be se to None if the trace hypotheses set changes. *)
  models : Constr.models option;
}


let pp ppf s =
  let open Fmt in
  let open Utils in
  pf ppf "@[<v 0>\
          @[<hov 2>Actions described:@ %a@]@;\
          @[<hv 0>Atoms:@ @[<v 0>%a@]@]@;\
          @[<hov 2>Trace constraints:@ %a@]@;\
          @[<hov 2>Formulas:@ %a@]@;\
            %a@.\
          %a@;@;@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") Action.pp_action)
    s.happens_hypotheses
    (pp_hypotheses pp_term_atom)
    s.message_hypotheses
    (pp_hypotheses pp_trace_formula)
    s.trace_hypotheses
    (pp_hypotheses pp_formula)
    s.formula_hypotheses
    (fun ppf i -> (styled `Bold ident) ppf (String.make i '-')) 40
    pp_formula
    s.formula

let init (goal : formula) =  {
  env = Vars.empty_env;
  happens_hypotheses = [];
  message_hypotheses = empty_hypotheses;
  trace_hypotheses =  empty_hypotheses ;
  formula_hypotheses = empty_hypotheses;
  formula = goal;
  trs = None;
  models = None;
}


let is_hypothesis f s =
  match formula_to_trace_formula f with
  | Some tf -> mem_hypotheses tf s.trace_hypotheses
  | None ->
    match f with
    | Atom (Message at) -> mem_hypotheses at s.message_hypotheses
    | _ ->  mem_hypotheses f s.formula_hypotheses

let select_message_hypothesis name s update =
  try
    let (hypo, hs) = select_and_update s.message_hypotheses name update in
    ({s with message_hypotheses = hs}, hypo.hypothesis)
  with Non_existing_hypothesis -> raise Not_found


let add_trace_formula tf s =
  { s with trace_hypotheses = add_hypothesis true () tf "tf" s.trace_hypotheses;
           models = None;}


(* Depending on the shape of the formula, we add it to the corresponding set of
   hypotheses. *)
let add_formula f s =
  match formula_to_trace_formula f with
  | Some tf -> { s with
                 trace_hypotheses =
                   add_hypothesis true () tf "tf" s.trace_hypotheses;
                 models = None;
               }
  | None ->
    match f with
    | Atom (Message at) ->
      { s with
        message_hypotheses =
          add_hypothesis true {t_euf = false} at "mess" s.message_hypotheses;
        trs = None
      }
    | _ ->  { s with formula_hypotheses =
                       add_hypothesis true () f "f" s.formula_hypotheses}

let get_eqs_neqs_at_list atl =
  List.map norm_xatom atl
  |> List.flatten
  |> List.fold_left (fun acc (od,a,b) ->
      add_xeq od (a,b) acc) ([],[],[])

let get_eqs_neqs s =
  let eqs, _, neqs = get_eqs_neqs_at_list
      (List.map (fun h -> h.hypothesis) (hypotheses_to_list s.message_hypotheses))
  in
  eqs,neqs

let update_trs s =
  let eqs,_ = get_eqs_neqs s in
  let trs = Completion.complete eqs in
  {s with trs = Some trs}

let get_trs s =
  match s.trs with
  | None -> let s = update_trs s in (s, opt_get s.trs)
  | Some trs -> (s, trs)


let message_atoms_valid s =
  let _, trs = get_trs s in
  let _, neqs = get_eqs_neqs s in
    (* The sequent is valid (at least) when equality hypotheses
     * imply a disequality hypothesis or an equality conclusion. *)
    List.exists
      (fun eq -> Completion.check_equalities trs [eq])
      (match s.formula with
         | Atom (Message (Eq,u,v)) -> (u,v)::neqs
         | _ -> neqs)

let set_env a s = { s with env = a }

let get_env s = s.env

let set_formula a s = { s with formula = a }

let get_formula s = s.formula

(* Return the conjunction of all trace hypotheses, together with
 * the possible negation of the conclusion formula if it is a trace
 * atom. *)
let make_trace_formula s =
 let trace_hypotheses =
   List.map (fun h -> h.hypothesis) (hypotheses_to_list s.trace_hypotheses)
 in
 List.fold_left
   (fun acc h -> Bformula.And (h,acc))
   Bformula.True
   (match s.formula with
      | Atom (Constraint atom) ->
          (Bformula.Not (Bformula.Atom atom)) :: trace_hypotheses
      | Formula.Not (Atom (Constraint atom)) ->
          (Bformula.Atom atom) :: trace_hypotheses
      | _ -> trace_hypotheses)

(** TODO  This is the only place where the model is computed,
  * and it is only called by functions that drop the sequent where
  * the model is cached, hence caching is useless. *)
let compute_models s =
  match s.models with
  | None ->
    let trace_hypotheses = make_trace_formula s in
    let models = Constr.models trace_hypotheses in
    { s with models = Some models;}
  | Some m -> s

let maximal_elems s tss =
  let s = compute_models s in
  Constr.maximal_elems (opt_get s.models) tss

let get_ts_equalities s =
  let s = compute_models s in
  let ts = Bformula.trace_formula_ts (make_trace_formula s)
           |> List.sort_uniq Pervasives.compare
  in
  Constr.get_equalities (opt_get (s.models)) ts

let constraints_valid s =
  let s = compute_models s in
  not (Constr.m_is_sat (opt_get s.models))

let get_all_terms s =
  let atoms =
    (List.map (fun h -> h.hypothesis) (hypotheses_to_list s.message_hypotheses))
  in
  List.fold_left (fun acc (_,a,b) -> a :: b :: acc) [] atoms
