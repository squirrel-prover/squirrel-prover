(* Generic functions to search illegal occurrences of names,
   and generate the appropriate proof obligations.
   Building upon Iter and Match.
   For use when writing tactics, eg gdh, fresh. *)

open Term
open Utils

module TS = TraceSequent
module ES = EquivSequent

module Hyps = TS.LocalHyps

type lsymb = Theory.lsymb

module MP = Match.Pos
module Sp = MP.Sp
module SE = SystemExpr


(*------------------------------------------------------------------*)
(* Functions handling macro expansion in terms, when allowed *)

(* information used to check if a macro can be expanded in a term:
   - the trace context
   - a tag indicating whether the occurrence is direct or indirect
     (for an indirect occurrence, the action producing it is recorded) *)

type occ_type =
  | EI_direct
  | EI_indirect of term

type expand_info = occ_type * Constr.trace_cntxt


(** expands t (not recursively) if it is a macro
    and we can check that its timestamp happens using info.
    Returns Some t' if t expands to t', None if no expansion was performed *)
let expand_macro_check_once ((ot, c):expand_info) (t:term) : term option =
  match t with
  | Macro (m, l, ts) ->
    if match ot with
      | EI_direct ->
        begin
          match c.models with
          | Some m -> Constr.query ~precise:true m [`Pos, `Happens ts]
          | None -> false
        end
      | EI_indirect _ -> true
      (* as long as we call on ioccs produced by fold_macro_support,
           invariant: expansion is always allowed *)
      (* we need to know that if a macro does not expand here,
          then it will be handled by another iocc *)
    then
      match Macros.get_definition c m ts with
      | `Def t' -> Some t'
      | `Undef | `MaybeDef -> None
    else
      None
  | _ -> None

(** expands t as much as possible, recursively
    (only at toplevel, not in subterms) *)
let rec expand_macro_check_all (info:expand_info) (t:term) : term =
  match expand_macro_check_once info t with
  | Some t' -> expand_macro_check_all info t'
  | None -> t




(*------------------------------------------------------------------*)
(* Functions to find all timestamps occurring in a term *)

(* Type of a timestamp occurrence *)
type ts_occ = Term.term Iter.occ

type ts_occs = ts_occ list


(** Check if [t1] is included in the patterm [pat2], i.e. [t1 ∈ occ2]. *)
let pat_subsumes
    (table : Symbols.table)
    (context : SE.context)
    ?(mv : Match.Mvar.t = Match.Mvar.empty)
    (t1 : term) (pat2 : term pat) 
  : Match.Mvar.t option
  =
  match Match.T.try_match ~mv table context t1 pat2
  with
  | FreeTyv | NoMatch _ -> None
  | Match mv -> Some mv


(** Check if the ts occurrence [occ2] subsumes [occ1], i.e. [occ1 ⊆ occ2].
    that's the case when occ1 is an instance of occ2, or when pred(occ1) is. *)
(* todo check that's sound, but it should be *)
let ts_occ_subsumes
    (table : Symbols.table)
    (system : SE.fset)
    ?(mv : Match.Mvar.t = Match.Mvar.empty)
    (occ1 : ts_occ)
    (occ2 : ts_occ) : bool =
                      (* for now, positions are not allowed here. *)
                      assert (Sp.is_empty occ1.occ_pos && Sp.is_empty occ2.occ_pos);
    
    let context = SE.reachability_context system in
    
    let pat2 = {
    pat_term = occ2.occ_cnt;
    pat_tyvars = [];
    pat_vars = Vars.Sv.of_list1 occ2.occ_vars; 
  } in

  let ps = pat_subsumes table context occ1.occ_cnt pat2 in
  let ps =
    if ps = None then
      pat_subsumes table context (mk_pred occ1.occ_cnt) pat2
    else
      ps 
  in

  match ps with
  | None -> false
  | Some mv ->
    (* start from the matching substitution [mv], and try to match all
       conditions of [pat1.occ_conds] with a conditions of
       [pat2.occ_conds], updating [mv] along the way if successful. *)
    let mv = ref mv in

    let mk_cond2 cond2 = Term.{ pat2 with pat_term = cond2; } in
    List.for_all (fun cond1 ->
        List.exists (fun cond2 ->
            match 
              pat_subsumes ~mv:(!mv) table context cond1 (mk_cond2 cond2)
            with 
            | None -> false
            | Some mv' -> mv := mv'; true
          ) occ2.occ_cond
      ) occ1.occ_cond



(** removes from l all elements that are subsumed by another.
    subsumes x y iff y subsumes x. *)
let clear_subsumed
    (subsumes : 'a -> 'a -> bool)
    (l : 'a list) :
  'a list =
  let ll =
    List.fold_left (fun acc x ->
        if List.exists (subsumes x) acc then
          acc
        else
          let acc =
            List.filter (fun y -> not (subsumes y x)) acc in
          x :: acc
      ) [] l
  in
  List.rev ll


(** removes from occs all elements that are subsumed by another *)
let clear_subsumed_ts
    (table : Symbols.table)
    (system : SE.fset)
    (occs : ts_occs) :
  ts_occs =
  clear_subsumed (ts_occ_subsumes table system) occs
    


  (** gathers all timestamps at which macros occur in a term. *)
  let get_actions_ext
      (t : Term.term)
      ?(fv:Vars.vars=[])
      (info:expand_info)
    : ts_occs =
    let (typ, contx) = info in
    let system = contx.system in
    let se = (SE.reachability_context system).set in
    let rec get (t : term)
        ~(fv:Vars.vars) ~(cond:Term.terms) ~(p:MP.pos) ~(se:SE.arbitrary)
      : ts_occs =
      match t with
      | Macro (m, l, ts) ->
        begin
          match expand_macro_check_once info t with
          | Some t' -> get ~fv ~cond ~p ~se t'
          | None -> 
            let ts = match Symbols.Macro.get_def m.s_symb contx.table with
              | Symbols.Input -> Term.mk_pred ts
              | _             -> ts
            in
            let occ = Iter.{
                occ_cnt  = ts;
                occ_vars = List.rev fv;
                occ_cond = cond;
                occ_pos  = Sp.empty; } (* we don't handle positions here for now *)
            in
            [occ] @ get ~fv ~cond ~p ~se ts
        end
      | _ ->
        MP.fold_shallow
          (fun t' se fv cond p occs ->
             occs @ (get t' ~fv ~cond ~p ~se))
          ~se ~fv ~p ~cond [] t
    in
    get t ~fv ~cond:[] ~p:MP.root ~se



(** Returns all timestamps occuring in macros in a list of terms.
    Should only be used when sources are directly occurring,
    not themselves produced by unfolding macros *)
let get_macro_actions
    (contx : Constr.trace_cntxt)
    (sources : terms) : ts_occs
  =
  let ei = (EI_direct, contx) in 
  let actions =
    List.concat_map (fun t -> get_actions_ext t ei) sources
  in
  let table = contx.table in
  let system = contx.system in
  clear_subsumed_ts table system actions




(*------------------------------------------------------------------*)
(* Occurrence of a name *)

(* information used to remember where an occurrence was found.
   - the name it's in collision with,
   - a subterm where it was found (for printing),
   - the type of occ (direct or indirect, with the action if indirect)
   - the timestamps in the source term in which the occurrence is found *) 
type occ_info = {oi_name:nsymb; oi_subterm:term; oi_occtype:occ_type; oi_source_ts: ts_occs}

(** constructs an occ_info *)
let mk_oinfo (m:nsymb) (st:term) (typ:occ_type) (ts:ts_occs) : occ_info =
  {oi_name = m; oi_subterm = st; oi_occtype = typ; oi_source_ts = ts}

type n_occ = nsymb Iter.occ
type name_occ = n_occ * occ_info
type name_occs = name_occ list


(** constructs a name occurrence *)
let mk_nocc (n:nsymb) (fv:Vars.vars) (cond:terms) (pos:Sp.t) : n_occ =
  Iter.{occ_cnt = n;
        occ_vars = fv;
        occ_cond = cond;
        occ_pos = pos;}


(** internally used to print a description of the occurrence *)
let pp_internal (ppf:Format.formatter) (occ:name_occ) : unit =
  let (occ, oinfo) = occ in
  match oinfo.oi_occtype with
  | EI_indirect a ->
    Fmt.pf ppf
      "%a @,(collision with %a)@ in action %a@ @[<hov 2>in term@ @[%a@]@]"
      Term.pp_nsymb occ.occ_cnt 
      Term.pp_nsymb oinfo.oi_name
      Term.pp a
      Term.pp oinfo.oi_subterm
  | EI_direct ->
    Fmt.pf ppf
      "%a @,(collision with %a)@ @[<hov 2>in term@ @[%a@]@]"
      Term.pp_nsymb occ.occ_cnt
      Term.pp_nsymb oinfo.oi_name
      Term.pp oinfo.oi_subterm

(** prints a description of the occurrence *)
let pp (ppf:Format.formatter) (occ:name_occ) : unit =
  Printer.pr "  @[<hv 2>%a@]@;@;" pp_internal occ



(*------------------------------------------------------------------*)
(* Occurrence subsumption (aka inclusion) *)

(** checks if all instances of [o1] are instances of [o2].
    [o1] and [o2] actions must have the same action name,
    [o1] and [o2] must also collide with the same name *)
let occ_incl
    (table : Symbols.table)
    (system : SE.fset)
    ((o1, oi1) : name_occ)
    ((o2, oi2) : name_occ)
  : bool =
  (* for now, positions not allowed here *)
  assert (Sp.is_empty o1.occ_pos && Sp.is_empty o2.occ_pos);

  (* build a dummy term, which we use to match in one go all elements of
     the two occurrences *)
  let mk_dummy ((o,oi):name_occ) =
    let n = o.occ_cnt in
    let phi_ac = match oi.oi_occtype with
      | EI_direct -> Term.mk_false
      | EI_indirect a -> Term.mk_eq ~simpl:false Term.init a
    in
    let phi_n = Term.mk_eq ~simpl:false (Term.mk_name n) (Term.mk_name n) in
    let phi_cond = Term.mk_ands ~simpl:false o.occ_cond in
    Term.mk_ands ~simpl:false [phi_ac; phi_n; phi_cond]
  in
  let pat2 = Term.{
      pat_tyvars = [];
      pat_vars   = Vars.Sv.of_list o2.occ_vars;
      pat_term   = mk_dummy (o2, oi2);
    }
  in  
  let context = SE.reachability_context system in
  match Match.T.try_match table context (mk_dummy (o1, oi1)) pat2 with
  | Match.FreeTyv | Match.NoMatch _ -> false
  | Match.Match _ ->
    (* we still need to check they are in collision with the same name, at the same timestamps *)
    oi1.oi_name = oi2.oi_name && oi1.oi_source_ts = oi2.oi_source_ts


(** Removes from [occs] occurrences that are subsumed by another. *)
let remove_subsumed_occs
    (table : Symbols.table)
    (system : SE.fset)
    (occs : name_occs) 
  : name_occs
  =
  clear_subsumed (occ_incl table system) occs


(*------------------------------------------------------------------*)
(* Functions to look for illegal name occurrences in a term *)

(** type of a function that takes a term, and generates
    a list of occurrences in it, each with the name it collides with
    and a subterm it was found in.
    Also returns an 'a list, used as an accumulator to keep
    any useful information gathered during the exploration of the term.
    Uses
    - a continuation unit -> (n_occ * nsymb * term) list * 'a list
       when it does not want to handle the term it's given,
       and just asks to be called again on the subterms
    - a continuation fv -> cond -> p -> se -> st -> term -> (n_occ * nsymb * term) list * 'a list,
       that calls the function again on the given parameters,
       for when it needs to do finer things
       (typically handle some of the subterms manually, and call this continuation
          on the remaining ones,
        or handle subterms at depth 1 by hand, and call the continuation on subterms at depth 2).
      Functions of this type don't need to unfold macros, that's handled separately. *)
type 'a f_fold_occs = 
  (unit -> (n_occ * nsymb * term) list * 'a list) -> (* continuation: give up and try again on subterms *)
  (fv:Vars.vars ->       (* continuation: to be called on strict subterms (for rec calls) *)
   cond:terms ->
   p:MP.pos ->           
   info:expand_info ->
   st:term ->
   term ->
   (n_occ * nsymb * term) list * 'a list)->         
  info:expand_info ->  (* info to expand macros, incl. system at current pos *)
  fv:Vars.vars ->      (* variables bound above the current position *)
  cond:terms ->        (* condition at the current position *)
  p:MP.pos ->          (* current position*)
  st:term ->           (* a subterm we're currently in (for printing purposes) *)
  term ->              (* term at the current position *)
  (n_occ * nsymb * term) list * 'a list (* found occurrences, and accumulator *)


(** given a f_fold_occs function get_bad_occs,
    calls get_bad_occs, is called again when get_bad_occs asks
    for recursive calls on subterms, and handles the case where
    get_bad_occs calls its first continuation (ie gives up)
    by 1) unfolding the term, if it's a macro that can be unfolded
       2) doing nothing, if it's a macro that can't be unfolded
          (in that case, fold_macro_support will generate a separate iocc 
          for that)
       2) using Match.Pos.fold_shallow, to recurse on subterms at depth 1. *)
let fold_bad_occs
    (get_bad_occs: 'a f_fold_occs)
    ~(fv:Vars.vars)
    (info:expand_info)
    (t:term) : (n_occ * nsymb * term) list * 'a list
  =
  let rec get
      ~(fv:Vars.vars) ~(cond:Term.terms) ~(p:MP.pos) ~(info:expand_info)
      ~(st:Term.term) 
      (t:term) : (n_occ * nsymb * term) list * 'a list
    =
    let typ, contx = info in
    let se = SE.to_arbitrary contx.system in
    (* the continuation to be passed to get_bad_occs for cases it does 
       not handle *)
    let retry_on_subterms () : (n_occ * nsymb * term) list * 'a list =
      match t with
      | Macro _ -> (* expand if possible *)
        begin
          match expand_macro_check_once info t with
          | Some t' -> get ~fv ~cond ~p ~info ~st t'
          | None -> ([], [])
          (* if we can't expand, fold_macro_support will create
              another iocc for that macro, and it will be checked
              separately *)
        end

      | _ -> 
        MP.fold_shallow
          (fun t' se fv cond p (occs, acc) ->
             let info = (typ, {contx with system = SE.to_fset se}) in
             let sst = if is_binder t then t' else st in
             let (newoccs, newacc) = get t' ~fv ~cond ~p ~info ~st:sst in
             (occs @ newoccs, acc @ newacc))
          ~se ~fv ~p ~cond ([], []) t
    in
    get_bad_occs retry_on_subterms get ~info ~fv ~cond ~p ~st t 
  in
  get ~fv ~cond:[] ~p:MP.root ~info ~st:t t



(*------------------------------------------------------------------*)
(** given a function find_occs that generates a list of occurrences found in
     a term, together with the name they collide with and a subterm they were found in,
     expanding macros when possible according to expand_info but
     not otherwise (undef and maybedef macros will be handled by 
     fold_macro_support);
    computes the list of all occurrences in the list of source terms.
    Also returns the accumulator.
    Relies on fold_macro_support to look through all macros in the term. *)
let find_occurrences
    ?(pp_ns: (unit Fmt.t) option=None)
    (find_occs : 
       (fv:Vars.vars ->
        expand_info ->
        term ->
        (n_occ * nsymb * term) list * 'a list))
    (contx : Constr.trace_cntxt)
    (env : Vars.env)
    (sources : terms) : name_occs * 'a list
  =
  let system = contx.system in
  let table = contx.table in

  let ppp ppf () = match pp_ns with
    | Some x -> Fmt.pf ppf "of %a " x ()
    | None   -> Fmt.pf ppf ""
  in

  (* direct occurrences of names in the wrong places *)
  let dir_occs, dir_acc =
    List.fold_left
      (fun (dir_occs, dir_acc) t -> (* find direct occurrences in t *)
         Printer.pr "@[<hv 2>Bad occurrences %afound@ directly in %a:@]@;"
           ppp ()
           Term.pp t;
         (* timestamps occurring in t *)
         let ts = get_macro_actions contx [t] in
         (* name occurrences in t *)
         let noccs, acc = find_occs ~fv:[] (EI_direct, contx) t in
         (* add the info *)
         let occs = List.map (fun (o, nn, st) -> (o, mk_oinfo nn st EI_direct ts)) noccs in
         (* printing *)
         List.iter (Printer.pr "%a" pp) occs;
         if occs = [] then
           Printer.pr "  (no occurrences)@;";
         dir_occs @ occs, dir_acc @ acc)
      ([], [])
      sources
  in
  
  (* indirect occurrences *)
  Printer.pr "@;@[<hv 2>Bad occurrences %afound@ in other actions:@]@;"
    ppp ();
  let ind_occs, ind_acc =
    Iter.fold_macro_support (fun iocc (ind_occs, ind_acc) ->
        (* todo: if fold_macro_support stored in iocc the fset
           for the place where the iocc was found, we could give it instead of contx to find_occs *)
        (* todo: we could find a way to print which source the indirect occs came from,
           not sure that's useful though *)
        let t = iocc.iocc_cnt in
        let sfv = iocc.iocc_vars in
        let src = iocc.iocc_sources in
        let a =
          mk_action iocc.iocc_aname (Action.get_indices iocc.iocc_action) 
        in
        (* a's free variables should always be in fv \cup env *)
        assert (Vars.Sv.subset (Vars.Sv.of_list (get_vars a)) (Vars.Sv.union sfv (Vars.to_set env))); 
        (* timestamps occurring in sources *)
        let ts = get_macro_actions contx src in
        (* indirect occurrences in iocc *)
        let noccs, acc = find_occs ~fv:(Vars.Sv.elements sfv) (EI_indirect a, contx) t in
        (* add the info *)
        let occs = List.map (fun (o, nn, st) -> (o, mk_oinfo nn st (EI_indirect a) ts)) noccs in
        ind_occs @ occs, ind_acc @ acc)
      contx env sources ([], [])
  in

  (* printing *)
  List.iter (Printer.pr "%a" pp) ind_occs;
  if ind_occs = [] then
    Printer.pr "  (no occurrences)@;";

  (* remove subsumed occs *)
  let occs = dir_occs @ ind_occs in
  let loccs = List.length occs in
  (* todo: this would need to change if the system depends on the occ *)
  let occs = remove_subsumed_occs table system occs in
  let loccs' = List.length occs in
  let lsub = loccs - loccs' in

  Printer.pr "@;Total: @[<v 0>%d bad occurrence%s@;" loccs (if loccs = 1 then "" else "s");
  Printer.pr "%d of them %s subsumed by another@;" lsub (if lsub = 1 then "is" else "are");
  Printer.pr "%d bad occurrence%s remaining@;@]@;" loccs' (if loccs' = 1 then "" else "s");
  occs, dir_acc @ ind_acc 




(* given a f_fold_occs,
   computes the list of all occurrences in sources,
   taking care of macro expansion and going through all terms,
   using fold_macro_support and map_fold *)   
let find_all_occurrences
    ?(pp_ns: (unit Fmt.t) option=None)
    (get_bad_occs: 'a f_fold_occs)
    (contx : Constr.trace_cntxt)
    (env : Vars.env)
    (sources : terms) : name_occs * 'a list
  =
  find_occurrences ~pp_ns (fold_bad_occs get_bad_occs) contx env sources



(*------------------------------------------------------------------*)
(* Proof obligations for a name occurrence *)

(** Constructs the formula
    "exists free vars.
      (exists t1.occ_vars. action ≤ t1.occ_cnt || 
       … || 
       exists tn.occ_vars. action ≤ tn.occ_cnt) &&
      conditions of occ && 
      indices of n = indices of occ"
    which will be the condition of the proof obligation when finding the 
    occurrence occ.
    action is the action producing the occ (optional, none for direct occs)
    ts=[t1, …, tn] are intended to be the timestamp occurrences in t.
    The free vars of occ.occ_cnt, action, and cond
    not bound in the sequent's env should be in occ.occ_vars,
    which is the case if occ was produced correctly
    (ie by Match.fold given either empty (for direct occurrences)
     or iocc_vars (for indirect occurrences).
    The free vars of ts should be all be bound in the sequent's env.
    If negate is set to true, returns instead the negation of that formula. *)
let occurrence_formula
    ?(negate : bool=false)
    (occ : name_occ)
  : term
  =
  let nocc, oinfo = occ in
  let n = nocc.occ_cnt in
  let n_fv = Vars.Sv.of_list1 nocc.occ_vars in
  let na = oinfo.oi_name in
  let ts = oinfo.oi_source_ts in

  let cond = nocc.occ_cond in
  let fv = Vars.Sv.elements n_fv in

  (* In addition to generating an equality formula for all indices of n and na, 
     we directly substitute those that are free variables. *)
  (* Produces logically equivalent, but simpler, formulas. *)
  (* We only do this in the "positive" case (ie  "there is a collision"),
     as it is less intuitive in the "negative" case since these are disequalities
     (though it would still be correct) *)
  let sigma = 
    List.filter_map (fun x -> x)
      (List.map2
         (fun i_n i_na ->
            if List.mem i_n fv then
              Some (ESubst (Term.mk_var i_n, Term.mk_var i_na))
            else None)
         n.s_indices na.s_indices)
  in
  let sub t = subst sigma t in
  let indices' = List.map (subst_var sigma) n.s_indices in
  let cond' = List.map sub cond in

  (* the equality formula is still needed, as eg if na.s_indices = (i, j)
     and n.s_indices' = (i', i'), having the substitution i' -> i loses the 
     fact that j = i' = i.
     So we keep all the equalities. Some become trivial but that's ok. *)
  let phi_eq =
    if not negate then
      mk_indices_eq ~simpl:true na.s_indices indices'
    else
      mk_indices_neq ~simpl:false na.s_indices n.s_indices
  in
  let phi_cond_eq =
    if not negate then
      mk_ands ~simpl:true (cond' @ [phi_eq])
    else
      mk_impl ~simpl:true (mk_ands ~simpl:true cond) phi_eq
  in 
  match oinfo.oi_occtype with
  | EI_indirect a ->
    (* indirect occurrence: we also generate the timestamp inequalities *)
    let a' = if not negate then sub a else a in
    (* no need to substitute ts since the variables we renamed do not 
       occur in ts *)
    let phis_time =
      List.map (fun (ti:ts_occ) ->
          mk_exists ~simpl:true
            ti.occ_vars
            (mk_timestamp_leq a' ti.occ_cnt)
        ) ts
    in
    let phi_time = mk_ors ~simpl:true phis_time in

    if not negate then
      mk_exists ~simpl:true fv (mk_and ~simpl:true phi_time phi_cond_eq)
    else
      mk_forall ~simpl:true fv (mk_impl ~simpl:true phi_time phi_cond_eq)

  | EI_direct -> (* direct occurrence *)
    if not negate then
      mk_exists ~simpl:true fv phi_cond_eq
    else
      mk_forall ~simpl:true fv phi_cond_eq




(*------------------------------------------------------------------*)
(* Proof obligations for name occurrences *)

(* given
   - a f_fold_occs function (see above)
   - a context (in particular, that includes the systems we want to use)
   - the environment
   - a list of sources where we search for occurrences
   - optionally, a pp_ns that prints what we look for (just for pretty printing)

  computes a list of formulas whose disjunction means "a bad occurrence happens"
   (or, alternatively, if negate is set to true,
   whose conjunction means "no bad occurrence happens")
   and an 'a list, which is an accumulator storing anything useful gathered
   by the 'a f_fold_occs when exploring the term *)
let occurrence_formulas
    ?(negate : bool=false)
    ?(pp_ns: (unit Fmt.t) option=None)
    (get_bad_occs: 'a f_fold_occs)
    (contx : Constr.trace_cntxt)
    (env : Vars.env)
    (sources : terms)
  : terms * 'a list
  =
  let occs, acc = find_all_occurrences ~pp_ns get_bad_occs contx env sources in
  (List.map (occurrence_formula ~negate) occs, acc)
 
