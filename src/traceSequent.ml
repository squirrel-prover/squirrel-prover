open Utils
open Atom

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

  val get_name_prefix : string -> string * int

  val select_and_update :
    remove:bool -> update:('a -> 'a) ->
    ('a, 'b) hypotheses -> string ->
    ('a, 'b) hypothesis * ('a, 'b) hypotheses

  val find_such_that :
    ('a, 'b) hypotheses ->
    (('a, 'b) hypothesis -> bool) ->
    ('a, 'b) hypothesis

  val remove_such_that :
    ('a, 'b) hypotheses ->
    (('a, 'b) hypothesis -> bool) ->
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
  
  let mk_name h id = h.name_prefix ^ string_of_int id
  
  let get_name_prefix name =
    match  String.split_on_integer name with
    | _, None -> raise Not_found
    | s, Some u -> s,u
  
  let get_visible hs =
    List.filter (fun h -> h.visible) hs
  
  let select_and_update ~remove ~update hs name =
    let rec aux id hsacc =
      match hsacc with
      | [] ->  raise Non_existing_hypothesis
      | p::q ->
        if name = mk_name p id then
          let p = { p with tag = update p.tag } in
          if remove then
            p, q
          else
            p, p::q
        else
          let res, new_hs = aux (id+1) q in
          res, p::new_hs
    in
    let name_prefix,_ = get_name_prefix name in
    let hs_list = M.find name_prefix hs in
    let res,new_hs_list = aux 0 (List.rev (get_visible hs_list)) in
    (res, M.add name_prefix (List.rev new_hs_list) hs)
  
  let find_such_that :
      type a b. (a,b) hypotheses -> ((a,b) hypothesis -> bool) -> 
      (a,b) hypothesis =
    fun hs test ->
    let exception Found of (a,b) hypothesis in
    try
      M.iter
        (fun _ l -> try raise (Found (List.find test l)) with Not_found -> ())
        hs ;
      raise Not_found
    with Found h -> h
  
  let remove_such_that :
      type a b. (a,b) hypotheses ->
                ((a,b) hypothesis -> bool) ->
                (a,b) hypothesis * (a,b) hypotheses =
    fun hs test ->
    let found = ref None in
    let f x =
      if !found = None && test x then begin
        found := Some x ;
        false
      end else
        true
    in
    let hs' = M.map (List.filter f) hs in
    match !found with
      | None -> raise Not_found
      | Some h -> h,hs'
  
  let select = M.iter
  
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
    let _,r2 = M.bindings hs |> List.split in
    List.flatten r2
  
  
  let mem f hs =
    M.exists (fun _ hs_list ->
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
    aux 0 (List.rev (get_visible hs_list))
  
  let map f hs =
    M.map (fun h -> List.map f h) hs
  
  let pp pp_formula id ppf hypo =
    Fmt.pf ppf "%s: %a@;" (mk_name hypo id) pp_formula hypo.hypothesis
  
  let pps pp_formula ppf hs =
    M.iter (fun _ hs_list ->
    List.iteri
      (fun i h -> pp pp_formula i ppf h)
      (List.rev (get_visible hs_list))) hs
end

let get_name_prefix = H.get_name_prefix

type message_hypothesis_tag = { t_euf : bool}

type trace_tag = unit

type formula_tag = unit

type message_hypothesis =
  (message_hypothesis_tag, message_atom) H.hypothesis

type message_hypotheses =
  (message_hypothesis_tag, message_atom) H.hypotheses

type trace_hypotheses = (trace_tag, trace_atom) H.hypotheses

type formula_hypotheses = (formula_tag, Term.formula) H.hypotheses

module S : sig
  type t = private {
    system : Action.system ;
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
    conclusion : Term.formula;
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

  val init_sequent : Action.system -> t

  (** Updates a sequent.
      [keep_trs] must be [true] only if the udates leaves the TRS associated to
      the sequent unchanged.
      Idem for [keep_models] and the models.
      [keep_trs] and [keep_models] default to [false]. *)
  val update :
    ?system:Action.system ->
    ?env:Vars.env ->
    ?happens_hypotheses:Term.timestamp list ->
    ?message_hypotheses:message_hypotheses ->
    ?trace_hypotheses:trace_hypotheses ->
    ?formula_hypotheses:formula_hypotheses ->
    ?conclusion:Term.formula ->
    ?keep_trs:bool ->
    ?keep_models:bool -> 
    t -> t

  (** Set the trs of a sequent. 
      Raise [Invalid_argument ..] if already set. *)
  val set_trs : t -> Completion.state -> t

  (** Set the models of a sequent. 
      Raise [Invalid_argument ..] if already set. *)
  val set_models : t -> Constr.models -> t
end = struct
  type t = {
    system : Action.system ;
    env : Vars.env;
    happens_hypotheses : Term.timestamp list;
    message_hypotheses : message_hypotheses;
    trace_hypotheses :  trace_hypotheses;
    formula_hypotheses : formula_hypotheses;
    conclusion : Term.formula;
    trs : Completion.state option;
    models : Constr.models option;
  }

  let init_sequent system = {
    system = system ;
    env = Vars.empty_env;
    happens_hypotheses = [];
    message_hypotheses = H.empty;
    trace_hypotheses =  H.empty ;
    formula_hypotheses = H.empty;
    conclusion = Term.True;
    trs = None;
    models = None;
  }

  let update ?system ?env ?happens_hypotheses
      ?message_hypotheses ?trace_hypotheses ?formula_hypotheses
      ?conclusion ?(keep_trs=false) ?(keep_models=false) t =
    let trs = 
      if keep_trs || message_hypotheses = None 
      then t.trs 
      else None 
    and models =
      if keep_models || trace_hypotheses = None 
      then t.models
      else None 
    in
    let system = Utils.opt_dflt t.system system
    and env    = Utils.opt_dflt t.env env
    and happens_hypotheses = 
      Utils.opt_dflt t.happens_hypotheses happens_hypotheses
    and message_hypotheses = 
      Utils.opt_dflt t.message_hypotheses message_hypotheses
    and trace_hypotheses = 
      Utils.opt_dflt t.trace_hypotheses trace_hypotheses
    and formula_hypotheses =
      Utils.opt_dflt t.formula_hypotheses formula_hypotheses
    and conclusion = 
      Utils.opt_dflt t.conclusion conclusion
    in
    {
      system = system ;
      env = env ;
      happens_hypotheses = happens_hypotheses ;
      message_hypotheses = message_hypotheses ;
      trace_hypotheses = trace_hypotheses ;
      formula_hypotheses = formula_hypotheses ;
      conclusion = conclusion ;
      trs = trs ;
      models = models ;
    }
  
  let set_trs t trs = match t.trs with
    | None -> { t with trs = Some trs; }
    | Some _ -> raise (Invalid_argument "traceSequent: trs already set")

  let set_models t models = match t.models with
    | None -> { t with models = Some models }
    | Some _ -> raise (Invalid_argument "traceSequent: models already set")
end

include S

type sequent = S.t

let pp ppf s =
  let open Fmt in
  pf ppf "@[<v 0>" ;
  pf ppf "@[System: %a@]@;"
    Action.pp_system s.system;
  if s.env <> Vars.empty_env then
    pf ppf "@[Variables: %a@]@;" Vars.pp_env s.env ;
  (* Print happens hypotheses *)
  if s.happens_hypotheses <> [] then
    pf ppf "@[<hov 2>Executed actions:@ %a@]@;"
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") Term.pp)
      s.happens_hypotheses ;
  (* Print message, trace and general hypotheses *)
  H.pps pp_message_atom ppf s.message_hypotheses ;

  H.pps pp_trace_atom ppf s.trace_hypotheses ;
  H.pps Term.pp ppf s.formula_hypotheses ;

  (* Print separation between hypotheses and conclusion *)
  styled `Bold ident ppf (String.make 40 '-') ;
  (* Print conclusion formula and close box. *)
  pf ppf "@;%a@]" Term.pp s.conclusion

let is_hypothesis f s =
  match f with
  | Term.Atom (#Atom.message_atom as at) -> H.mem at s.message_hypotheses
  | Term.Atom (#Atom.trace_atom as at) -> H.mem at s.trace_hypotheses
  | Term.Atom (`Happens t) -> List.mem t s.happens_hypotheses
  | _ ->  H.mem f s.formula_hypotheses

let get_trace_atoms s=
    List.map (fun h -> h.H.hypothesis) (H.to_list s.trace_hypotheses)

let get_hypothesis id s =
  try (H.find id s.formula_hypotheses).H.hypothesis with Not_found ->
    try
      Term.Atom ((H.find id s.message_hypotheses).H.hypothesis :>
               Atom.generic_atom)
    with Not_found ->
          Term.Atom ((H.find id s.trace_hypotheses).H.hypothesis :>
               Atom.generic_atom)

let id = fun x -> x

let select_message_hypothesis ?(remove=false) ?(update=id) name s =
  try
    let (hypo, hs) =
      H.select_and_update s.message_hypotheses name ~remove ~update
    in
    (S.update ~message_hypotheses:hs s, hypo.H.hypothesis)
  with H.Non_existing_hypothesis -> raise Not_found

let select_formula_hypothesis ?(remove=false) ?(update=id) name s =
  try
    let (hypo, hs) =
      H.select_and_update s.formula_hypotheses name ~remove ~update
    in
    (S.update ~formula_hypotheses:hs s, hypo.H.hypothesis)
  with H.Non_existing_hypothesis -> raise Not_found

let find_formula_hypothesis pred s =
  let pred h = pred h.H.hypothesis in
  let hypo = H.find_such_that s.formula_hypotheses pred in
    hypo.H.hypothesis

let remove_formula_hypothesis pred s =
  let pred h = pred h.H.hypothesis in
  let hypo,hs = H.remove_such_that s.formula_hypotheses pred in
    (hypo.H.hypothesis, S.update ~formula_hypotheses:hs s)

let remove_trace_hypothesis pred s =
  let pred h = pred h.H.hypothesis in
  let hypo,hs = H.remove_such_that s.trace_hypotheses pred in
    (hypo.H.hypothesis, S.update ~trace_hypotheses:hs s)

let remove_message_hypothesis pred s =
  let pred h = pred h.H.hypothesis in
  let hypo,hs = H.remove_such_that s.message_hypotheses pred in
    (hypo.H.hypothesis, S.update ~message_hypotheses:hs s)

let add_trace_hypothesis ?(prefix="T") s tf =
  S.update ~trace_hypotheses:(H.add true () tf prefix s.trace_hypotheses) s

class iter_macros ~system f = object (self)
  inherit Iter.iter ~system as super
  method visit_message t =
    match t with
      | Term.Macro ((m,sort,is),[],a) ->
          if List.for_all
               Vars.(function EVar v -> not (is_new v))
               (Term.get_vars t) &&
             Macros.is_defined m a
          then
            let def = Macros.get_definition system sort m is a in
              f t def ;
              self#visit_message def
      | t -> super#visit_message t
  method visit_formula f =
    (* Do not visit macros. When a macro formula is defined we could add
     * an hypothesis stating the equivalence between the macro and its
     * expansion. But we'll probably take care of that later as part of a
     * larger redesign of the macro expansion system. *)
    match f with
      | Term.Macro ((m,sort,is),[],a) -> ()
      | t -> super#visit_formula t
end

(** Add to [s] equalities corresponding to the expansions of all macros
  * occurring in [at]. *)
let rec add_macro_defs s at =
  let macro_eqs : message_atom list ref = ref [] in
  let iter =
    new iter_macros
      ~system:s.system
      (fun t t' -> macro_eqs := `Message (`Eq,t,t') :: !macro_eqs)
  in
    iter#visit_formula (Term.Atom at) ;
    List.fold_left
      (add_message_hypothesis ~prefix:"D")
      s
      !macro_eqs

and add_message_hypothesis ?(prefix="M") s at =
  (* if we are reinserting a previously introduced formula, we change the
     prefix. *)
  let prefix = if prefix = "H" then "M" else prefix in
  if H.mem at s.message_hypotheses then s else
    let mh = H.add true {t_euf = false} at prefix s.message_hypotheses in
    let s : S.t = S.update ~message_hypotheses:mh s in
    add_macro_defs s (at :> generic_atom)

let rec add_happens s ts =
  let s =
    S.update ~happens_hypotheses:(ts :: s.happens_hypotheses) s
  in
    match ts with
      | Term.Action (symb,indices) ->
          let a = Action.of_term symb indices in
          let system = s.system in
          add_formula ~prefix:"C"
               (snd (Action.get_descr system a).Action.condition)
            s
      | _ -> s

(* Depending on the shape of the formula, we add it to the corresponding set of
   hypotheses. *)
and add_formula ?prefix f s =
  match f with
  | Term.Atom (#Atom.message_atom as at) -> add_message_hypothesis ?prefix s at
  | Term.Atom (#Atom.trace_atom as at) -> add_trace_hypothesis ?prefix s at
  | Term.Atom (`Happens ts) -> add_happens s ts
  | Term.And(a, b) -> let s = add_formula ?prefix a s in add_formula ?prefix b s
  | _ ->
    let prefix = match prefix with Some p -> p | None -> "H" in
    S.update ~formula_hypotheses:(H.add true () f prefix s.formula_hypotheses) s

let get_eqs_neqs_at_list atl =
  List.fold_left
    (fun acc (`Message (od,a,b)) -> add_xeq_eq od (a,b) acc)
    ([],[]) atl

let get_eqs_neqs s =
  get_eqs_neqs_at_list
    (List.map (fun h -> h.H.hypothesis) (H.to_list s.message_hypotheses))

let get_trs s =
  let update_trs s =
    let eqs,_ = get_eqs_neqs s in
    let trs = Completion.complete eqs in
    S.set_trs s trs
  in
  match s.trs with
  | None -> let s = update_trs s in (s, opt_get s.trs)
  | Some trs -> (s, trs)


let message_atoms_valid s =
  let _, trs = get_trs s in
  let _, neqs = get_eqs_neqs s in
  List.exists
    (fun eq -> Completion.check_equalities trs [eq])
    neqs

let set_env a s = S.update ~env:a s

let get_env s = s.env

let system s = s.system

let set_system system s = S.update ~system:system s 

let pi projection s =
  let pi_term t = Term.pi_term ~projection t in
  S.update
    ~conclusion:(pi_term s.conclusion)
    ~message_hypotheses:(
      H.map
        (function
          | { H.hypothesis = `Message (o,s,t) } as h ->
            { h with H.hypothesis = `Message (o, pi_term s, pi_term t) })
        s.message_hypotheses)
    ~formula_hypotheses:(
      H.map
        (function
          | { H.hypothesis = f } as h ->
            { h with H.hypothesis = pi_term f })
        s.formula_hypotheses)
    ~keep_trs:false
    ~keep_models:false
    s

let set_conclusion a s =
  let s = S.update ~conclusion:a s in
    match a with
      | Term.Atom (#message_atom as at) -> add_macro_defs s at
      | _ -> s

let init ~system (goal : Term.formula) =
  set_conclusion goal (init_sequent system)

let get_conclusion s = s.conclusion

let apply_subst subst s =
  let mess_is_triv m =
    match m with
    | `Message (`Eq,t1,t2) when t1=t2 -> true
    | _ -> false
  in
  let trace_is_triv (m:trace_atom) : bool =
    match m with
    | `Timestamp (`Eq,t1,t2) when t1=t2 -> true
    | `Index (`Eq,i1,i2) when i1=i2 -> true
    | _ -> false
  in
  let apply_hyp_subst f is_triv hypo =
    let new_formula = f hypo.H.hypothesis in
    {hypo with H.visible = not(is_triv new_formula);
               H.hypothesis = new_formula}
  in
  S.update
   ~message_hypotheses:(
     H.map (apply_hyp_subst (Atom.subst_message_atom subst)
              mess_is_triv) s.message_hypotheses)
   ~trace_hypotheses:(
     H.map (apply_hyp_subst (Atom.subst_trace_atom subst)
              trace_is_triv) s.trace_hypotheses)
   ~formula_hypotheses:(
     H.map (apply_hyp_subst
              (Term.subst subst)
              (fun _ -> false)) s.formula_hypotheses)
   ~conclusion:(Term.subst subst s.conclusion)
   s

let get_models s =
  let update_models s =
    match s.models with
    | None ->
      let trace_atoms = get_trace_atoms s in
      let models = Constr.models_conjunct trace_atoms in
      S.set_models s models
    | Some _ -> s
  in
  let s = update_models s in
  s, opt_get s.models

let maximal_elems s tss =
  let s,models = get_models s in
  s, Constr.maximal_elems models tss

let get_ts_equalities s =
  let s,models = get_models s in
  let ts = trace_atoms_ts (get_trace_atoms s) in
  s, Constr.get_ts_equalities models ts

let get_ind_equalities s =
  let s,models = get_models s in
  let inds = trace_atoms_ind (get_trace_atoms s) in
  s, Constr.get_ind_equalities models inds

let constraints_valid s =
  let s,models = get_models s in
  not (Constr.m_is_sat models)

let get_all_terms s =
  let atoms =
    List.map (fun h -> h.H.hypothesis) (H.to_list s.message_hypotheses)
  in
  let atoms =
    match s.conclusion with
      | Term.Atom (#message_atom as at) -> at::atoms
      | _ -> atoms
  in
  List.fold_left (fun acc (`Message (_,a,b)) -> a :: b :: acc) [] atoms
