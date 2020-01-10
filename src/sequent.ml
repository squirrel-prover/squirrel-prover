open Utils
open Term
open Atom
open Bformula
open Formula

(* The generic type for hypothesis, with arbtitry type of formulas and tag. *)

module H : sig

  type ('a, 'b) hypothesis = {
    name_prefix : string;
    tag :  'a;
    hypothesis : 'b;
    visible : bool;
  }

  exception Non_existing_hypothesis

  type ('a, 'b) hypotheses

  val empty :  ('a, 'b) hypotheses

  val select_and_update :
    remove:bool -> update:('a -> 'a) ->
    ('a, 'b) hypotheses -> string ->
    ('a, 'b) hypothesis * ('a, 'b) hypotheses

  val to_list : ('a, 'b) hypotheses -> ('a, 'b) hypothesis list

  val add : bool ->
    'a -> 'b -> string -> ('a, 'b) hypotheses -> ('a, 'b) hypotheses

  val mem : 'b -> ('a, 'b) hypotheses -> bool

  val find : string -> ('a, 'b) hypotheses -> ('a, 'b) hypothesis

  val map :  ( ('a, 'b) hypothesis ->  ('a, 'b) hypothesis)
    -> ('a, 'b) hypotheses -> ('a, 'b) hypotheses

  val pp : (Format.formatter -> 'a -> unit) -> int ->
    Format.formatter -> ('b, 'a) hypothesis -> unit

  val pps : (Format.formatter -> 'a -> unit) ->
    Format.formatter -> ('b, 'a) hypotheses -> unit

end = struct

type ('a, 'b) hypothesis = {
  name_prefix : string;
  tag :  'a;
  hypothesis : 'b;
  visible : bool;
}


exception Non_existing_hypothesis

module M = Map.Make(String)

(* A set of hypotheses is made of two maps. One maps hypothesis names
   (according to [name]) to variables, and the second maps
   name prefixes to the current largest name_suffix for this
   name_prefix. *)
type ('a, 'b) hypotheses = (('a,'b) hypothesis list) M.t

let empty =  M.empty

let mk_name h id = (h.name_prefix)^(string_of_int id)

let get_name_prefix name =
  match  String.split_on_integer name with
  | s, None -> raise Not_found
  | s, Some u -> s,u

let get_visible hs =
  List.filter (fun h -> h.visible) hs

let select_and_update ~remove ~update hs name =
  let rec aux id hsacc =
    match hsacc with
    | [] ->  raise Non_existing_hypothesis
    | p::q ->
      let new_p,remainder =
        if name = (mk_name p id) then
          let p = { p with tag = update p.tag } in
          p, q
        else
          let res,l = (aux (id+1) q) in
          res, l
      in
      if remove then
        new_p,remainder
      else
        new_p,new_p :: remainder
  in
  let name_prefix,_ = get_name_prefix name in
  let hs_list = M.find name_prefix hs in
  let res,new_hs_list = aux 0 (List.rev (get_visible hs_list)) in
  (res, M.add name_prefix new_hs_list hs)

let add visible tag hypo name_prefix hs : ('a, 'b) hypotheses =
  let v = { name_prefix = name_prefix;
            hypothesis = hypo;
            tag = tag;
            visible = visible;
          }
  in
  try
    let hs_list = M.find name_prefix hs in
    (* we only add the formula if it is a fresh one. *)
    let res = if List.mem v hs_list then hs_list else v::hs_list in
    M.add name_prefix res hs
  with Not_found -> M.add name_prefix ([v]) hs

let to_list hs =
  let r1,r2 = M.bindings hs |> List.split in
  List.flatten r2


let mem f hs =
  M.exists (fun name hs_list ->
      List.exists (fun hypo -> hypo.hypothesis = f) hs_list)
    hs

let find name hs =
  let rec aux id hs =
    match hs with
    | [] -> raise Not_found
    | p :: q -> if mk_name p id = name then p else aux (id+1) q
  in
  let name_prefix,_ = get_name_prefix name in
  let hs_list = M.find name_prefix hs in
  aux 0 hs_list

let map f hs =
  M.map (fun h -> List.map f h) hs

let pp pp_formula id ppf hypo =
  Fmt.pf ppf "%s: %a@;" (mk_name hypo id) pp_formula hypo.hypothesis

let pps pp_formula ppf hs =
  M.iter (fun name hs_list ->
  List.iteri
    (fun i h -> pp pp_formula i ppf h)
    (List.rev (get_visible hs_list))) hs
end

type message_hypothesis_tag = { t_euf : bool}

type trace_tag = unit

type formula_tag = unit

type message_hypothesis = (message_hypothesis_tag, term_atom) H.hypothesis

type message_hypotheses = (message_hypothesis_tag, term_atom) H.hypotheses
type trace_hypotheses = (trace_tag, trace_formula) H.hypotheses
type formula_hypotheses = (formula_tag, formula) H.hypotheses

type t = {
  env : Vars.env;
    (** Must contain all free variables of the sequent,
      * which are logically understood as universally quantified. *)
  happens_hypotheses : Term.timestamp list;
    (** Hypotheses of the form [happens(t)]. *)
  message_hypotheses : message_hypotheses;
    (** Equalities and disequalities over messages. *)
  trace_hypotheses :  trace_hypotheses;
    (** Quantifier-free formula over index and timestamp predicates. *)
  formula_hypotheses : formula_hypotheses;
    (** Other hypotheses. *)
  conclusion : formula;
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
type sequent = t

let pp ppf s =
  let open Fmt in
  let open Utils in
  pf ppf "@[<v 0>" ;
  if s.env <> Vars.empty_env then
    pf ppf "@[Variables: %a@]@;" Vars.pp_typed_env s.env ;
  (* Print happens hypotheses *)
  if s.happens_hypotheses <> [] then
    pf ppf "@[<hov 2>Executed actions:@ %a@]@;"
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") Term.pp_timestamp)
      s.happens_hypotheses ;
  (* Print message, trace and general hypotheses *)
  H.pps pp_term_atom ppf s.message_hypotheses ;
  H.pps pp_trace_formula ppf s.trace_hypotheses ;
  H.pps pp_formula ppf s.formula_hypotheses ;
  (* Print separation between hypotheses and conclusion *)
  styled `Bold ident ppf (String.make 40 '-') ;
  (* Print conclusion formula and close box. *)
  pf ppf "@;%a@]" pp_formula s.conclusion

let init_sequent = {
  env = Vars.empty_env;
  happens_hypotheses = [];
  message_hypotheses = H.empty;
  trace_hypotheses =  H.empty ;
  formula_hypotheses = H.empty;
  conclusion = Formula.True;
  trs = None;
  models = None;
}

let is_hypothesis f s =
  match formula_to_trace_formula f with
  | Some tf -> H.mem tf s.trace_hypotheses
  | None ->
    match f with
    | Atom (#Atom.term_atom as at) -> H.mem at s.message_hypotheses
    | Atom (`Happens t) -> List.mem t s.happens_hypotheses
    | _ ->  H.mem f s.formula_hypotheses

let get_hypothesis id s =
  try (H.find id s.formula_hypotheses).H.hypothesis with Not_found ->
    try
      Atom ((H.find id s.message_hypotheses).H.hypothesis :>
               Atom.generic_atom)
    with Not_found ->
      Formula.bformula_to_foformula
        (fun x -> (x :> Atom.generic_atom))
        (H.find id s.trace_hypotheses).H.hypothesis

let id = fun x -> x

let select_message_hypothesis ?(remove=false) ?(update=id) name s =
  try
    let (hypo, hs) =
      H.select_and_update s.message_hypotheses name ~remove ~update
    in
    ({s with message_hypotheses = hs}, hypo.H.hypothesis)
  with H.Non_existing_hypothesis -> raise Not_found

let select_formula_hypothesis ?(remove=false) ?(update=id) name s =
  try
    let (hypo, hs) =
      H.select_and_update s.formula_hypotheses name ~remove ~update
    in
    ({s with formula_hypotheses = hs}, hypo.H.hypothesis)
  with H.Non_existing_hypothesis -> raise Not_found

let add_trace_formula ?(prefix="T") tf s =
  { s with
    trace_hypotheses = H.add true () tf prefix s.trace_hypotheses;
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
      (fun t t' -> macro_eqs := `Message (`Eq,t,t') :: !macro_eqs)
  in
    iter#visit_fact (Atom at) ;
    List.fold_left
      (add_message_hypothesis ~prefix:"D")
      s
      !macro_eqs

and add_message_hypothesis ?(prefix="M") s at =
  if H.mem at s.message_hypotheses then s else
    let s =
      { s with
        message_hypotheses =
          H.add true {t_euf = false} at prefix s.message_hypotheses;
        trs = None }
    in
    add_macro_defs s at

let rec add_happens s ts =
  let s =
    { s with happens_hypotheses = ts :: s.happens_hypotheses }
  in
    match ts with
      | TName (symb,indices) ->
          let a = Action.of_term symb indices in
          add_formula ~prefix:"C"
            (Formula.bformula_to_foformula
               (fun x -> (x :> Atom.generic_atom))
               (snd (Action.get_descr a).Action.condition))
            s
      | _ -> s

(* Depending on the shape of the formula, we add it to the corresponding set of
   hypotheses. *)
and add_formula ?prefix f s =
  match formula_to_trace_formula f with
  | Some tf -> add_trace_formula ?prefix tf s
  | None ->
    match f with
    | Atom (#Atom.term_atom as at) -> add_message_hypothesis ?prefix s at
    | Atom (`Happens ts) -> add_happens s ts
    | _ ->
        let prefix = match prefix with Some p -> p | None -> "H" in
        { s with formula_hypotheses =
                   H.add true () f prefix s.formula_hypotheses }

let get_eqs_neqs_at_list atl =
  List.fold_left
    (fun acc (`Message (od,a,b)) -> add_xeq_eq od (a,b) acc)
    ([],[]) atl

let get_eqs_neqs s =
  get_eqs_neqs_at_list
    (List.map (fun h -> h.H.hypothesis) (H.to_list s.message_hypotheses))

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
      (match s.conclusion with
         | Atom (`Message (`Eq,u,v)) -> (u,v)::neqs
         | _ -> neqs)

let set_env a s = { s with env = a }

let get_env s = s.env

let set_conclusion a s =
  let s = { s with conclusion = a } in
    match a with
      | Atom (#term_atom as at) -> add_macro_defs s at
      | _ -> s

let init (goal : formula) = set_conclusion goal init_sequent

let get_conclusion s = s.conclusion

let apply_subst subst s =
  let mess_is_triv m =
    match m with
    | `Message (`Eq,t1,t2) when t1=t2 -> true
    | _ -> false
  in
  let trace_is_triv (m:trace_formula) : bool =
    match m with
    | Atom (`Timestamp (`Eq,t1,t2)) when t1=t2 -> true
    | Atom (`Index (`Eq,i1,i2)) when i1=i2 -> true
    | _ -> false
  in
  let apply_hyp_subst f is_triv hypo =
    let new_formula = f hypo.H.hypothesis in
    {hypo with H.visible = not(is_triv new_formula);
               H.hypothesis = new_formula}
  in
  {s with
   message_hypotheses = H.map (apply_hyp_subst (Atom.subst_term_atom subst)
                                 mess_is_triv) s.message_hypotheses;
   trace_hypotheses = H.map (apply_hyp_subst
                               (Bformula.subst_trace_formula subst)
                                 trace_is_triv) s.trace_hypotheses;
   formula_hypotheses = H.map (apply_hyp_subst
                                 (Formula.subst_formula subst)
                                 (fun _ -> false)) s.formula_hypotheses;
   conclusion = Formula.subst_formula subst s.conclusion;
  }
(* Return the conjunction of all trace hypotheses, together with
 * the possible negation of the conclusion formula if it is a trace
 * atom. *)
let make_trace_formula s =
 let trace_hypotheses =
   List.map (fun h -> h.H.hypothesis) (H.to_list s.trace_hypotheses)
 in
 List.fold_left
   (fun acc h -> Bformula.And (h,acc))
   Bformula.True
   (match Formula.formula_to_trace_formula s.conclusion with
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

let get_models s =
  let s = compute_models s in
  opt_get s.models

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
    List.map (fun h -> h.H.hypothesis) (H.to_list s.message_hypotheses)
  in
  let atoms =
    match s.conclusion with
      | Atom (#term_atom as at) -> at::atoms
      | _ -> atoms
  in
  List.fold_left (fun acc (`Message (_,a,b)) -> a :: b :: acc) [] atoms
