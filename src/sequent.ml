open Utils
open Action
open Term
open Bformula
open Formula

(* The generic type for hypothesis, with arbtitry type of formulas and tag. *)
type ('a, 'b) hypothesis = {
  name_prefix : string;
  name_suffix : int;
  tag :  'a;
  hypothesis : 'b;
  visible : bool;
}

let name hypo =
  Fmt.strf "%s%i" hypo.name_prefix hypo.name_suffix

exception Non_existing_hypothesis

module M = Map.Make(String)


(* A set of hypotheses is made of two maps. One maps hypothesis names
   (according to [name]) to variables, and the second maps
   name prefixes to the current largest name_suffix for this
   name_prefix. *)
type ('a, 'b) hypotheses = ((('a,'b) hypothesis) M.t * int M.t)

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
  Fmt.pf ppf "%s: %a@;" (name hypo) pp_formula hypo.hypothesis

let pp_hypotheses pp_formula ppf hs =
  List.iter
    (fun h -> if h.visible then pp_hypothesis pp_formula ppf h)
    (hypotheses_to_list hs)

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
    (** Must contain all free variables of the sequent,
      * which are logically understood as universally quantified. *)
  happens_hypotheses : action list;
    (** Hypotheses of the form [happens(t)]. *)
  message_hypotheses : message_hypotheses;
    (** Equalities and disequalities over messages. *)
  trace_hypotheses :  trace_hypotheses;
    (** Quantifier-free formula over index and timestamp predicates. *)
  formula_hypotheses : formula_hypotheses;
    (** Other hypotheses. *)
  formula : formula;
    (** The conclusion / right-hand side formula of the sequent. *)
  trs : Completion.state option;
    (** Either [None], or the term rewriting system
      * corresponding to the current message hypotheses.
      * Must be se to [None] if message hypotheses change. *)
  models : Constr.models option;
    (** Either [None], or the models corresponding to the current
      * trace hypotheses.
      * Must be set to [None] if trace hypotheses change. *)
}

let pp ppf s =
  let open Fmt in
  let open Utils in
  pf ppf "@[<v 0>" ;
  (* Print happens hypotheses *)
  if s.happens_hypotheses <> [] then
    pf ppf "@[<hov 2>Executed actions:@ %a@]@;"
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") Action.pp_action)
      s.happens_hypotheses ;
  (* Print message, trace and general hypotheses *)
  pp_hypotheses pp_term_atom ppf s.message_hypotheses ;
  pp_hypotheses pp_trace_formula ppf s.trace_hypotheses ;
  pp_hypotheses pp_formula ppf s.formula_hypotheses ;
  (* Print separation between hypotheses and conclusion *)
  styled `Bold ident ppf (String.make 40 '-') ;
  (* Print conclusion formula and close box. *)
  pf ppf "@;%a@]" pp_formula s.formula

let init_sequent = {
  env = Vars.empty_env;
  happens_hypotheses = [];
  message_hypotheses = empty_hypotheses;
  trace_hypotheses =  empty_hypotheses ;
  formula_hypotheses = empty_hypotheses;
  formula = Formula.True;
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
  { s with
    trace_hypotheses = add_hypothesis true () tf "T" s.trace_hypotheses;
    models = None }

class iter_macros f = object (self)
  inherit Iter.iter as super
  method visit_term t =
    match t with
      | Macro ((m,is),[],a) ->
          if Macros.is_defined m a then
            let def = Macros.get_definition m is a in
              f t def ;
              self#visit_term def
      | t -> super#visit_term t
end

(** Add to [s] equalities corresponding to the expansions of all macros
  * occurring in [at]. *)
let rec add_macro_defs s at =
  let macro_eqs : term_atom list ref = ref [] in
  let iter =
    new iter_macros
      (fun t t' -> macro_eqs := (Eq,t,t') :: !macro_eqs)
  in
    iter#visit_fact (Atom at) ;
    List.fold_left
      (add_message_hypothesis ~prefix:"D")
      s
      !macro_eqs

and add_message_hypothesis ?(prefix="M") s at =
  if mem_hypotheses at s.message_hypotheses then s else
    let s =
      { s with
        message_hypotheses =
          add_hypothesis true {t_euf = false} at prefix s.message_hypotheses;
        trs = None }
    in
    add_macro_defs s at

(* Depending on the shape of the formula, we add it to the corresponding set of
   hypotheses. *)
let add_formula f s =
  match formula_to_trace_formula f with
  | Some tf -> add_trace_formula tf s
  | None ->
    match f with
    | Atom (Message at) -> add_message_hypothesis s at
    | _ ->
        { s with formula_hypotheses =
                   add_hypothesis true () f "H" s.formula_hypotheses }

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

let set_formula a s =
  let s = { s with formula = a } in
    match a with
      | Atom (Message at) -> add_macro_defs s at
      | _ -> s

let init (goal : formula) = set_formula goal init_sequent

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
   (match Formula.formula_to_trace_formula s.formula with
      | Some f -> (Bformula.Not f) :: trace_hypotheses
      | None -> trace_hypotheses)

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
