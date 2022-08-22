(* Generic functions to search illegal occurrences of names,
   and generate the appropriate proof obligations.
   Building upon Iter and Match.
   For use when writing tactics, eg gdh, fresh. *)

open Term
open Utils

module TS = TraceSequent

module Hyps = TS.LocalHyps

type lsymb = Theory.lsymb

module MP = Match.Pos
module Sp = MP.Sp
module SE = SystemExpr


(*------------------------------------------------------------------*)
(* Functions handling macro expansion in terms, when allowed *)

(* information used to check if a macro can be expanded in a term.
     - the current sequent, for direct occurrences; 
     - the action for the iocc that produced the term, for indirect ones;
     - and in any case the trace context. *)
type expand_info = 
  | EI_direct   of TS.sequent * Constr.trace_cntxt
  | EI_indirect of term * Constr.trace_cntxt

(** gets the sequent for the direct occurrence we're looking at *)
let get_sequent (info:expand_info) : TS.sequent option =
  match info with
  | EI_direct (s,_) -> Some s
  | _ -> None

(** gets the action for the iocc that produced the term we're looking at *)
let get_action (info:expand_info) : term option =
  match info with
  | EI_indirect (a,_) -> Some a
  | _ -> None

(** gets the trace context *)
let get_context (info:expand_info) : Constr.trace_cntxt =
  match info with
  | EI_indirect (_, c) -> c
  | EI_direct (_, c) -> c


(** expands t if it is a macro and we can check that its timestamp happens
    using info (not recursively).
    Returns Some t' if t expands to t', None if no expansion was performed *)
let expand_macro_check_once (info:expand_info) (t:term) : term option =
  match t with
  | Macro (m, l, ts) ->
     if match info with
        | EI_direct (s, _) -> TS.query_happens ~precise:true s ts
        | EI_indirect (a, _) -> true (* ts = a is unsound *)
     (* checking the shape may be better?
         as long as we call on ioccs produced by fold_macro_support,
         invariant: expansion is always allowed *)
     (* we need to know that if a macro does not expand here,
         then it will be handled by another iocc *)
     then
       match Macros.get_definition (get_context info) m ts with
       | `Def t' -> Some t'
       | `Undef | `MaybeDef -> None
     else
       None
  | _ -> None

(** expands t as much as possible, recursively
    (only at toplevel, not in subterms) *)
let rec expand_macro_check_all (info:expand_info) (t:term) : term =
  match t with
  | Macro (m, l, ts) ->
     if match info with
        | EI_direct (s, _) -> TS.query_happens ~precise:true s ts
        | EI_indirect (a, _) -> true
     then
       match Macros.get_definition (get_context info) m ts with
       | `Def t' -> expand_macro_check_all info t'
       | `Undef | `MaybeDef -> t
     else
       t
  | _ -> t


(** returns (u, v) such that t = (u = v), or None if not possible.
    (unfolds the macros when possible) *) 
let destr_eq_expand
      (info:expand_info)
      (t:term) : (term * term) option =
  let t' = expand_macro_check_all info t in
  if not (Term.is_eq t') then None
  else Term.destr_eq t'



(*------------------------------------------------------------------*)
(* Functions to find all timestamps occurring in a term *)

(** Exception raised when a forbidden occurrence of a message variable
    is found. *)
exception Var_found


(* Type of a timestamp occurrence *)
type ts_occ = Term.term Iter.occ

type ts_occs = ts_occ list


(** removes from occs all occurrences that are subsumed by another.
    occ1 subsumes occ2 if they are equal
    or if occ1 is essentially pred(occ2) *)
let clear_subsumed_timestamps (occs : ts_occs) : ts_occs =
  let subsumes (occ1 : ts_occ) (occ2 : ts_occ) =
    (* for now, positions are not allowed here. *)
    assert (Sp.is_empty occ1.occ_pos && Sp.is_empty occ2.occ_pos);

    (* Future work: alpha-renaming *)
    List.length occ1.occ_vars = 
      List.length occ2.occ_vars &&
        List.for_all2 (=) occ1.occ_vars occ2.occ_vars &&
          occ1.occ_cond = occ2.occ_cond &&
            (occ1.occ_cnt = occ2.occ_cnt || occ1.occ_cnt = Term.mk_pred occ2.occ_cnt)
  in
  let occs =
    List.fold_left (fun acc occ ->
        let acc = List.filter (fun occ' -> not (subsumes occ occ')) acc in
        if List.exists (fun occ' -> subsumes occ' occ) acc
        then acc
        else occ :: acc
      ) [] occs
  in
  List.rev occs


(** gathers all timestamps at which macros occur in a term. *)
let get_actions_ext
      (contx : Constr.trace_cntxt)
      (t : Term.term)
      ?(fv:Vars.vars=[])
      (info:expand_info)
    : ts_occs =
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


  
(** returns all timestamps occuring in macros in a list of terms *)
let get_macro_actions
      (contx : Constr.trace_cntxt)
      (sources : (term * expand_info) list) : ts_occs
  =
  let actions =
    List.concat_map (fun (t, ei) -> get_actions_ext contx t ei) sources
  in
  clear_subsumed_timestamps actions




(*------------------------------------------------------------------*)
(* Occurrence of a name *)

(* information used to remember where an occurrence was found.
   - the name it's in collision with,
   - a subterm where it was found (for printing),
   - optionally the action producing the iocc where
     it was found, for indirect occs *) 
type occ_info = {oi_name:nsymb; oi_subterm:term; oi_action:term option}

(** constructs an occ_info *)
let mk_oinfo ?(ac:term option=None) (m:nsymb) (st:term) : occ_info =
  {oi_name = m; oi_subterm = st; oi_action = ac}

type name_occ = (nsymb * occ_info) Iter.occ
type name_occs = name_occ list


(** constructs a name occurrence *)
let mk_nocc (n:nsymb) (info:occ_info) 
      (fv:Vars.vars) (cond:terms) (pos:Sp.t) : name_occ =
  Iter.{occ_cnt = (n, info);
        occ_vars = fv;
        occ_cond = cond;
        occ_pos = pos;}


(** internally used to print a description of the occurrence *)
let pp_internal (ppf:Format.formatter) (occ:name_occ) : unit =
  let (n, oinfo) = occ.occ_cnt in
  match oinfo.oi_action with
  | Some a ->
     Fmt.pf ppf
       "%a @,(collision with %a)@ in action %a@ @[<hov 2>in term@ @[%a@]@]"
       Term.pp_nsymb n 
       Term.pp_nsymb oinfo.oi_name
       Term.pp a
       Term.pp oinfo.oi_subterm
  | None ->
     Fmt.pf ppf
       "%a @,(collision with %a)@ @[<hov 2>in term@ @[%a@]@]"
       Term.pp_nsymb n 
       Term.pp_nsymb oinfo.oi_name
       Term.pp oinfo.oi_subterm

(** prints a description of the occurrence *)
let pp (ppf:Format.formatter) (occ:name_occ) : unit =
  Printer.pr "  @[<hv 2>%a@]@;@;" pp_internal occ

(** prints a description of a subsumed occurrence *)
let pp_sub (ppf:Format.formatter) (occ:name_occ) : unit =            
  Printer.pr "  @[<hv 2>(subsumed) %a@]@;@;" pp_internal occ
  

(*------------------------------------------------------------------*)
(* Occurrence subsumption (aka inclusion) *)

(** checks if all instances of [o1] are instances of [o2].
    [o1] and [o2] actions must have the same action name,
    [o1] and [o2] must also collide with the same name *)
let occ_incl
      (table : Symbols.table)
      (system : SE.fset)
      (o1 : name_occ)
      (o2 : name_occ)
    : bool =
  (* for now, positions not allowed here *)
  assert (Sp.is_empty o1.occ_pos && Sp.is_empty o2.occ_pos);

  (* build a dummy term, which we use to match in one go all elements of
     the two occurrences *)
  let mk_dummy (o:name_occ) =
    let n, oi = o.occ_cnt in
    let phi_ac = match oi.oi_action with
      | None -> Term.mk_false
      | Some a -> Term.mk_eq ~simpl:false Term.init a
    in
    let phi_n = Term.mk_eq ~simpl:false (Term.mk_name n) (Term.mk_name n) in
    let phi_cond = Term.mk_ands ~simpl:false o.occ_cond in
    Term.mk_ands ~simpl:false [phi_ac; phi_n; phi_cond]
  in
  let pat2 = Term.{
        pat_tyvars = [];
        pat_vars   = Vars.Sv.of_list o2.occ_vars;
        pat_term   = mk_dummy o2;
             }
  in  
  let context = SE.reachability_context system in
  match Match.T.try_match table context (mk_dummy o1) pat2 with
  | Match.FreeTyv | Match.NoMatch _ -> false
  | Match.Match _ -> (* we still need to check they are in collision with the same name *)
     let (_, oi1),(_, oi2) = o1.occ_cnt, o2.occ_cnt in 
     oi1.oi_name = oi2.oi_name


(** adds [occ] to [occs], if it is not redundant.
    Removes from [occs] all occurrences subsumed by [occ].
    Returns the new occurrence list, and a list of now subsumed occurrences *)
let add_occ
      (table : Symbols.table)
      (system : SE.fset)
      (occ : name_occ)
      (occs : name_occs)
      (subsumed_occs : name_occs)
    : name_occs * name_occs
  =
  if List.exists (fun occ' -> occ_incl table system occ occ') occs
  then (occs, occ::subsumed_occs)
  else
    (* remove any old case which is subsumed by [occ] *)
    let (l,ll) =
      List.fold_left
        (fun (notsubs, newsubs) occ' ->
          if occ_incl table system occ' occ then
            (notsubs, occ' :: newsubs)
          else
            (occ'::notsubs, newsubs))
        ([], [])
        occs
    in
    (List.rev (occ::l), subsumed_occs @ (List.rev ll))



(** Removes from [occs] some occurrences that are subsumed by another.
    Returns [(occs', subsumed_occs)] that form a partition of [occs]
    such that all occurrences in [subsumed_occs] are subsumed by some [occ] in [occs'],
    and none of [occs'] is. *)
let partition_subsumed_occs
      (table : Symbols.table)
      (system : SE.fset)
      (occs : name_occs) 
    : name_occs * name_occs
  =
  List.fold_left
    (fun (occs', subsumed) occ ->
      add_occ table system occ occs' subsumed)
    ([], [])
    occs


(*------------------------------------------------------------------*)
(* Utility functions for lists of nsymbs *)

(** looks for a name with the same symbol in the list *)
let exists_symb (n:nsymb) (ns:nsymb list) : bool =
  List.exists (fun nn -> n.s_symb = nn.s_symb) ns


(** finds all names with the same symbol in the list *)
let find_symb (n:nsymb) (ns:nsymb list) : nsymb list =
  List.filter (fun nn -> n.s_symb = nn.s_symb) ns


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
    The free vars of ts should be all be bound in the sequent's env. *)
let occurrence_formula
      (ts  : ts_occs)
      (occ : name_occ)
    : term
  =
  let n, oinfo = occ.occ_cnt in
  let n_fv = Vars.Sv.of_list1 occ.occ_vars in
  let na = oinfo.oi_name in

  let cond = occ.occ_cond in
  let fv = Vars.Sv.elements n_fv in

  (* in addition to generating an equality formula for all indices of n and na, 
     we directly substitute those that are free variables *)
  (* produces logically equivalent, but simpler, formulas *)
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
  let phi_eq = mk_indices_eq ~simpl:true na.s_indices indices' in
  let phi_cond_eq = mk_ands ~simpl:true (cond' @ [phi_eq]) in

  match oinfo.oi_action with
  | Some a ->
    (* indirect occurrence: we also generate the timestamp inequalities *)
    let a' = sub a in
    (* no need to substitute ts since the variables we renamed do not 
       occur in ts *)
    let phis_time =
      List.map (fun (ti:ts_occ) ->
          mk_exists ~simpl:true
            ti.occ_vars
            (mk_leq ~simpl:true a' ti.occ_cnt)
        ) ts
    in
    let phi_time = mk_ors ~simpl:true phis_time in
    (* print the occurrence *)
    Printer.pr "%a" pp occ;
    mk_exists ~simpl:true fv (mk_and ~simpl:true phi_time phi_cond_eq)

  | None -> (* direct occurrence *)
       Printer.pr "%a" pp occ;
       mk_exists ~simpl:true fv phi_cond_eq



(** Constructs the proof obligation (trace sequent) for a direct or indirect 
    occurrence, stating that it suffices to prove the goal assuming
    the occurrence occ is equal to the name it collides with. *)
let occurrence_sequent
      (ts  : ts_occs)
      (s   : TS.sequent)
      (occ : name_occ)
    : TS.sequent
  = 
  TS.set_goal
    (mk_impl ~simpl:false
       (occurrence_formula ts occ)
       (TS.goal s))
    s


(*------------------------------------------------------------------*)
(** given
    - a function find_occs that generates a list of occurrences found in
      a term, expanding macros when possible according to expand_info but
      not otherwise (undef and maybedef macros will be handled by 
      fold_macro_support);
    - the sequent s of the current goal;
    - the term t where we look for occurrences;
    - optionally, a printer that prints a description of what we're looking
      for;
   computes the list of corresponding proof obligations: we now have 
      to prove s under the assumption that at least one of the found 
      occurrences must be an actual collision.
      Relies on fold_macro_support to look through all macros in the term. *)
let occurrence_sequents
    ?(pp_ns: (unit Fmt.t) option=None)
    (find_occs : 
       (se:SE.arbitrary ->
        fv:Vars.vars ->
        expand_info ->
        term ->
        name_occs))
    (s : TS.sequent)
    (t : Term.term) : TS.sequents 
  =
  let table = TS.table s in
  let contx = TS.mk_trace_cntxt s in
  let system = contx.system in
  let env = TS.vars s in

  let se = (SE.reachability_context system).set in
  let ppp ppf () = match pp_ns with
    | Some x -> Fmt.pf ppf "of %a " x ()
    | None   -> Fmt.pf ppf ""
  in
  let ts = get_macro_actions contx [t, EI_direct (s, contx)] in

  (* direct occurrences of names in the wrong places *)
  Printer.pr "@[<v 0>@[<hv 2>Bad occurrences %afound@ directly in %a:@]@;"
    ppp ()
    Term.pp t;

  let all_dir_occs = find_occs ~se ~fv:[] (EI_direct (s,contx)) t in
  (* remove occs that are subsumed by another *) 
  let dir_occs, subsumed_dir_occs =
    partition_subsumed_occs table system all_dir_occs 
  in

  (* proof obligations from the direct occurrences *)
  let direct_sequents = List.map (occurrence_sequent ts s) dir_occs in

  (* print subsumed occs separately *)
  List.iter (Printer.pr "%a" pp_sub) subsumed_dir_occs;

  if List.length all_dir_occs = 0 then
    Printer.pr "  (no occurrences)@;";


  (* indirect occurrences and their proof obligations *)
  Printer.pr "@;@;@[<hv 2>Bad occurrences %afound@ in other actions:@]@;"
    ppp ();
  let indirect_sequents, nsub =
    Iter.fold_macro_support (fun iocc (indirect_sequents, nsub) ->
        let t = iocc.iocc_cnt in
        let sfv = iocc.iocc_vars in
        let a =
          mk_action iocc.iocc_aname (Action.get_indices iocc.iocc_action) 
        in
        (* a's free variables should always be in fv *)
        assert (Vars.Sv.subset (Vars.Sv.of_list (get_vars a)) (Vars.Sv.union sfv (Vars.to_set env))); 
        
        (* indirect occurrences in iocc *)
        let all_ind_occs =
          find_occs ~se ~fv:(Vars.Sv.elements sfv)
            (EI_indirect (a, contx)) t
        in

        (* remove occs that are subsumed by another *) 
        let ind_occs, subsumed_ind_occs =
          partition_subsumed_occs table system all_ind_occs in

        (* proof obligations for the indirect occurrences *)
        let ss = List.rev_append 
                   (List.map (occurrence_sequent ts s) ind_occs)
                   indirect_sequents
        in

        (* print subsumed occs separately *)
        List.iter (Printer.pr "%a" pp_sub) subsumed_ind_occs;
        (ss, nsub + (List.length subsumed_ind_occs)))
      contx env [t] ([], List.length subsumed_dir_occs)
  in

  if List.length indirect_sequents = 0 then
    Printer.pr "  (no occurrences)@;";

  let nseq = 
    List.length direct_sequents + List.length indirect_sequents
  in

  Printer.pr "@;Total: %d bad occurrence%s (%d subsumed)@;@]"
    nseq (if nseq = 1 then "" else "s") nsub;

  direct_sequents @ List.rev indirect_sequents



(*------------------------------------------------------------------*)
(* Functions to look for illegal name occurrences in a term *)
(* Useful to construct the find_occs function for occurrence_sequents *)

(** type of a function that takes a term, and generates
    a list of occurrences in it, using
    - a continuation unit -> name_occs
       when it does not want to handle the term it's given,
       and just asks to be called again on the subterms
    - a continuation fv -> cond -> p -> se -> st -> term -> name_occs,
       for when it needs to do some work on the term, and needs to
       call fold_bad_occs again on some of its subterms.
      These functions are for use in fold_bad_occs and occurrence_goals.
      They don't need to unfold macros, that's handled separately. *)
type f_fold_occs = 
  (unit -> name_occs) -> (* continuation: give up and try again on subterms *)
  (fv:Vars.vars ->       (* continuation: to be called on strict subterms 
                            (for rec calls) *)
   cond:terms ->
   p:MP.pos ->           
   se:SE.arbitrary ->   
   st:term ->            
   term ->               
   name_occs) ->         
  se:SE.arbitrary ->   (* system at the current position *)
  info:expand_info ->  (* info to expand macros *)
  fv:Vars.vars ->      (* variables bound above the current position *)
  cond:terms ->        (* condition at the current position *)
  p:MP.pos ->          (* current position*)
  st:term ->           (* a subterm we're currently in (for printing purposes) *)
  term ->              (* term at the current position *)
  name_occs            (* found occurrences *)


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
    (get_bad_occs: f_fold_occs)
    ~(se:SE.arbitrary)
    ~(fv:Vars.vars)
    (info:expand_info)
    (t:term) : name_occs 
  =
  let rec get
            ~(fv:Vars.vars) ~(cond:Term.terms) ~(p:MP.pos) ~(se:SE.arbitrary) 
            ~(st:Term.term) 
            (t:term) : name_occs 
    =
    (* the continuation to be passed to get_bad_occs for cases it does 
       not handle *)
    let retry_on_subterms () : name_occs =
      match t with
      | Macro _ -> (* expand if possible *)
         begin
           match expand_macro_check_once info t with
           | Some t' -> get ~fv ~cond ~p ~se ~st t'
           | None -> []
         (* if we can't expand, fold_macro_support will create
             another iocc for that macro, and it will be checked
             separately *)
         end

      | _ -> 
         MP.fold_shallow
           (fun t' se fv cond p occs ->
             let sst = if is_binder t then t' else st in
             occs @ (get t' ~fv ~cond ~p ~se ~st:sst))
           ~se ~fv ~p ~cond [] t
    in
    get_bad_occs retry_on_subterms get ~info ~fv ~cond ~p ~se ~st t 
  in
  get ~fv ~cond:[] ~p:MP.root ~se ~st:t t


(*------------------------------------------------------------------*)
(** given
    - a f_fold_occs function get_bad_occs;
    - the sequent s of the current goal;
    - the term t where we look for occurrences;
    - optionally, a printer that prints a description of what we're looking for;
      computes the list of proof obligations: we now have to prove s
      under the assumption that at least one of the found occurrences must
      be an actual collision.*)
let occurrence_goals
      ?(pp_ns: (unit Fmt.t) option=None)
      (get_bad_occs: f_fold_occs)
      (s:TS.sequent)
      (t:term) : TS.sequents 
  =
  occurrence_sequents (fold_bad_occs get_bad_occs) s t
