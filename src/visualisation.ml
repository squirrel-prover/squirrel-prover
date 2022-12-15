(** {2 Nodes list} 

    Compute the list of timestamps happening and group them into equality
    classes.

    TODO:
    - when adding a term, add all the terms on which the former term depends;
    - when there is no model, do not compute anything but report a useful
      message to the user;
    - provide the user with the ability to visualize all the elements of
      an equality class;
    - dump more precise information about relationships: currently we only
      document non-strict inequalities, but it would be useful to visualize
      when they are strict.
*)

(** Get the non-repeating list of timestamps appearing in hypotheses of sequent
    [j], plus init. *)
let get_timstamps (j : LowTraceSequent.t) : Term.terms =
  let load (set : Term.St.t) (lit : Term.Lit.literal) =
    match Term.Lit.ty lit, lit with
    | Type.Timestamp, (_, Comp(_, ts1, ts2)) ->
        (Term.St.add ts1) @@ (Term.St.add ts2) @@ set
    | Type.Timestamp, (_, Happens(ts)) ->
        Term.St.add ts set
    | _, _ -> set
  in
  let hyps = LowTraceSequent.get_trace_hyps j in
  let atoms = Hyps.get_atoms_of_hyps hyps in
  let set = List.fold_left load (Term.St.singleton Term.init) atoms in
  Term.St.elements set

(** [get_classes_rep models terms] finds the equivalence classes [terms]
    according to [models].
    In each class, a term is chosen as representative.
    This choice follows this priority : Action > Pred(_) > Variable *)
let get_classes_rep (models : Constr.models) (terms : Term.terms) : Term.terms =
  let rec best_candidate (var_candidate : Term.term option) (pred_candidate : Term.term option)
    (terms : Term.terms) : Term.term =
    match terms, var_candidate, pred_candidate with
    | (Action _ as term) :: _l, _, _ ->
        term
    | (Var _ as term) :: l, _, _ ->
        best_candidate (Some term) pred_candidate l
    | (Fun (fsymb, _, [_t]) as term) :: l, _, _ when fsymb = Term.f_pred ->
        best_candidate var_candidate (Some term) l
    | [], _, Some term ->
        term
    | [], Some term, None ->
        term
    | _ ->
        assert(false)
  in
  let classes = Constr.get_ts_equalities ~precise:true models terms in
  List.map (best_candidate None None) classes



(** {2 Relations between nodes}
    Compute inequalities between timestamps. *)

(** Type to store dependence relation between terms:
    t1 <= t2 iff t2 is in the set stored with key t1.*)
type dependence = Term.St.t Term.Mt.t

(** Return an empty dependence *)
let empty : dependence =
  Term.Mt.empty

(** Add a new term in the dependence without relation *)
let add_node (t : Term.term) (dep : dependence) : dependence =
  Term.Mt.add t (Term.St.empty) dep

(** Add the new relation [t1] <= [t2] in the dependency *)
let add_edge (t1 : Term.term) (t2 : Term.term) (dep : dependence) : dependence =
  Term.Mt.add t1 (Term.St.add t2 (Term.Mt.find t1 dep)) dep

(** Remove relations t1 <= t3 in [dependence] such that there is t2 such that:
    t1 <= t2 && t2 <= t3. *)
let remove_transitive (dep : dependence) : dependence =
  let get_succ_of_succ (t1 : Term.term) : Term.St.t =
    Term.St.fold (fun t2 acc -> Term.St.union (Term.Mt.find t2 dep) acc) (Term.Mt.find t1 dep) Term.St.empty
  in
  Term.Mt.mapi (fun t set -> Term.St.diff set (get_succ_of_succ t)) dep

(** [build_dependence models l] is the object representing
    relations between terms in [l] according to [models]. *)
let build_dependence models (l : Term.terms) : dependence =
  let empty_dep = List.fold_left (fun dep t -> add_node t dep) empty l in
  let dep = List.fold_left 
    (fun dep1 t1 -> List.fold_left 
      (fun dep2 t2 ->
        let query = [(`Pos,Term.Lit.Comp(`Leq, t1, t2))] in
        if t1 <> t2 && Constr.query ~precise:true models query then
          add_edge t1 t2 dep2
        else
          dep2
      )
      dep1 l
    )
    empty_dep l in
  remove_transitive dep



(** {2 Layout}
    Compute the layout of the visualisation *)

(** Type to store, for each timestamp t1, the number of timestamps t2 such that:
    t2 < t1 *)
type counter = int Term.Mt.t

(** [incr_counter t counter] returns [counter] with the value of term [t] increased by 1. *)
let incr_counter (t : Term.term) (counter : counter) : counter =
  Term.Mt.add t ((Term.Mt.find t counter) + 1) counter

(** [decr_counter t counter] returns [counter] with the value of term [t] decreased by 1. *)
let decr_counter (t : Term.term) (counter : counter) : counter =
  Term.Mt.add t ((Term.Mt.find t counter) - 1) counter

(** [get_counter dep] returns the counter corresponding to the relation represented by [dep] *)
let get_counter (dep : dependence) : counter =
  let empty_counter = Term.Mt.map (fun _ -> 0) dep in
  Term.Mt.fold (fun _ set counter -> Term.St.fold (fun t counter -> incr_counter t counter) set counter) dep empty_counter

(** [get_top_layer dep counter] returns a pair:
    - The second part of the pair is the list of term such that ther counter is zero.
      These nodes do not depend on any other timestamps and will be printed on the top layer.
    - The first part of the pair is the counter from which
      we removed nodes from the top_layer and decreased the value of their children*)
let get_top_layer (dep : dependence) (counter : counter) : counter * Term.term list =
  let store (t : Term.term) (c : int) (acc : counter * Term.term list) : counter * Term.term list =
    let (counter, l) = acc in
    if c = 0 then
      let new_counter = Term.St.fold decr_counter (Term.Mt.find t dep) counter in
      (Term.Mt.remove t new_counter, t :: l)
    else
      acc
  in
  Term.Mt.fold store counter (counter, [])

(** [get_layout dep counter] returns a list.
    Each element correspond to a layer in the visualisation.
    Terms in the first list are on the top layer, and so on. *)
let get_layout (dep : dependence) : Term.term list list =
  let rec aux (dep : dependence) (counter : counter) : Term.term list list =
    if Term.Mt.is_empty counter then
      []
    else
      let (new_counter, l) = get_top_layer dep counter in
      l :: (aux dep new_counter)
  in
  aux dep (get_counter dep)


(** {2 Print JSON} *)

(** Print a comma and a line break. *)
let pp_comma ppf () =
  Format.fprintf ppf ",@;"

(** Print an HTML line break. *)
let pp_br ppf () =
  Format.fprintf ppf "<br>"

(** Print a term with HTML format. *)
let pp_term ppf term = 
  Format.fprintf ppf "%a"
    (Printer.html Term.pp) term
    
(** Print the id of a term. This id is based on its hash. *)
let pp_term_id ppf term = 
  Format.fprintf ppf "\"n%d\""
    (Term.hash term)

(** Print a state update with HTML format: [state] := [term] *)
let pp_update ppf (state,args,term) =
  Format.fprintf ppf "%a(%a) := %a"
    Term.pp_msymb_s state
    Vars.pp_list args
    pp_term term

(** If [opt] is [Some value], print the line "[property]": "[value]".
    The element [value] is printed by the function [pp] *)
let pp_option pp ppf (property, opt) =
  match opt with
  | Some value ->
      Format.fprintf ppf "\"%s\": \"%a\",@;"
        property
        pp value
  | None -> ()

(** Print the node corresponding to term [t].
    [cntxt] and [dependence] are used to find informations about [t] *)
let pp_node (cntxt : Constr.trace_cntxt) (dep : dependence) ppf (t : Term.term) =
  let mk_option condition value =
    if condition then
      Some value
    else
      None
  in
  (*We read in [cntxt] to find if the timestamp represented by [t] has some condition, state updates or output.*)
  let (cond, state, output) = match t with
    | Term.Action (asymb, idx) ->
        let action = Action.of_term asymb idx cntxt.table in
        let descr, subst = SystemExpr.descr_of_action cntxt.table cntxt.system action in
        let descr = Action.subst_descr subst descr in
        (
          mk_option (not (Term.f_triv (snd descr.condition))) (snd descr.condition),
          mk_option (descr.updates <> []) descr.updates,
          mk_option (fst descr.output <> Symbols.dummy_channel) (snd descr.output)
        )
    | _ -> (None, None, None)
  in
  (*We search in [dep] the children of [t]*)
  let children = Term.St.elements (Term.Mt.find t dep) in
  Format.fprintf ppf "@[<v 2>{@;\"id\": %a,@;\"name\": \"%a\",@;%a%a%a@[<v 2>\"children\": [@;%a@]@;]@]@;}"
    pp_term_id t (*property "id"*)
    pp_term t (*property "name"*)
    (pp_option pp_term) ("cond", cond)
      (*property "cond", if there is a condition*)
    (pp_option (Format.pp_print_list ~pp_sep:pp_br pp_update)) ("state", state)
      (*property "state", if there is at least a state update*) 
    (pp_option pp_term) ("output", output)
      (*property "output", if there is an output*)
    (Format.pp_print_list ~pp_sep:pp_comma pp_term_id) children
      (*property "children". Only print children's id.*)

(** Print the property "nodes" of the data. *)
let pp_nodes (cntxt : Constr.trace_cntxt) (dep : dependence) ppf (l : Term.terms) =
  Format.fprintf ppf "@[<v 2>\"nodes\": [@;%a@]@;]"
    (Format.pp_print_list ~pp_sep:pp_comma (pp_node cntxt dep)) l
  
(** Print a layer of the layout. *)
let pp_layer ppf layer =
  Format.fprintf ppf "@[<v 2>[@;%a@]@;]"
    (Format.pp_print_list ~pp_sep:pp_comma pp_term_id) layer

(** Print the property "layout" of the data. *)
let pp_layout ppf (layout : Term.term list list) =
  Format.fprintf ppf "@[<v 2>\"layout\": [@;%a@]@;]"
    (Format.pp_print_list ~pp_sep:pp_comma pp_layer) layout



(** {2 Main} *)

(** Print the data for the visualisation of the trace sequent [j] in JSON format. *)
let pp ppf j =
  let cntxt = LowTraceSequent.mk_trace_cntxt j in
  match cntxt.models with
  | Some models ->
      let terms = get_classes_rep models (get_timstamps j) in
      let dep = build_dependence models terms in
      let layout = get_layout dep in
      Format.fprintf ppf "@[<v 2>{@;%a,@;%a@]@;}@?"
        (pp_nodes cntxt dep) terms
        pp_layout layout
  | None -> ()
