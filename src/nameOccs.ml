(* Generic functions to search illegal occurrences of names,
   and generate the appropriate proof obligations.
   Building upon Iter and Match.
   For use when writing tactics, eg gdh, fresh. *)

open Term
open Utils

type lsymb = Theory.lsymb

module MP = Match.Pos
module Sp = MP.Sp
module SE = SystemExpr



(*------------------------------------------------------------------*)
(** Generic types and functions to handle occurrences of anything,
    with associated data and conditions, source timestamps, etc. *)
(* probably somewhat redundant with Iter.occ… but more specific to the use case here *)


(** Simple occurrence of an element of type 'a, with additional data of type 'b *)
(* Remarks:
   1) we could store a position in the term where the occ was, as in Iter.occ,
      but we don't use it anywhere for now
   2) we could store the fset at the point where the occ was found, which would
      be more precise (we would need to prove the goal for the occ only in that fset)
      (though since fold_macro_support does not give us the fset where the iocc is,
      we would still potentially be a little imprecise).
      we'll see if that's an issue later, for now we don't do that. *) 
type ('a, 'b) simple_occ = 
  {so_cnt     : 'a;        (* content of the occurrence *)
   so_coll    : 'a;        (* thing it potentially collides with *)
   so_ad      : 'b;        (* additional data, if needed *)
   so_vars    : Vars.vars; (* variables bound above the occurrence *)
   so_cond    : terms;     (* condition above the occurrence *)
   so_subterm : term;      (* a subterm where the occurrence was found (for printing) *)
  }

type ('a, 'b) simple_occs = (('a, 'b) simple_occ) list


(** constructs a simple occurrence *)
let mk_simple_occ
    (cnt:'a) (coll:'a) (ad:'b)
    (vars:Vars.vars) (cond:terms) (st:term) : ('a, 'b) simple_occ = 
  {so_cnt=cnt; so_coll=coll; so_ad=ad; so_cond=cond; so_vars=vars; so_subterm=st}


(** Type of a timestamp occurrence *)
type ts_occ = (term, unit) simple_occ
type ts_occs = ts_occ list


(** Type of empty simple occurrences (used as dummy parameter when they are not needed) *)
type empty_occ = (unit, unit) simple_occ
type empty_occs = empty_occ list


(** Label indicating whether an occurrence is direct or indirect, and
   if so which action produced it *)
type occ_type =
  | EI_direct
  | EI_indirect of term


(** Extended occurrence, with additional info about where it was found *)
type ('a, 'b) ext_occ =
  {eo_occ       : ('a, 'b) simple_occ;
   eo_occtype   : occ_type;             (* direct/indirect+action *)
   eo_source    : terms;                (* original term where the occ was found *) 
   eo_source_ts : ts_occs }             (* timestamps occurring in the source term *)

type ('a, 'b) ext_occs = (('a, 'b) ext_occ) list


(** Functions to turn content and data into terms, so they can be 
    compared by matching. (we could have one function 'a -> 'a -> 'b -> term 
    instead, if needed later *)
type ('a, 'b) converter = { conv_cnt:'a -> term; conv_ad: 'b -> term }

(** Converter for timestamps *)
let ts_converter : (term, unit) converter =
  {conv_cnt=(fun x -> x); conv_ad=(fun () -> mk_false)}

(** Converter for names *)
let name_converter : (nsymb, unit) converter =
  {conv_cnt=mk_name; conv_ad=(fun () -> mk_false)}

(** Dummy converter for empty occurrences *)
let empty_converter : (unit, unit) converter =
  {conv_cnt=(fun () -> mk_false); conv_ad=(fun () -> mk_false)}


(*------------------------------------------------------------------*)
(** Occurrence subsumption/inclusion *)
(** occ1 included in occ2 MUST mean that (occ1 is a collision) \/ (occ2 is a collision) <=> (occ2 is a collision) *)
(** so that we only need to look at occ2 *)
(** ie occ1 is an instance of occ2, in an instance of its action, with a STRONGER condition *)
(** (not weaker!!) *)


(** Checks if [t1] is included in the patterm [pat2], i.e. [t1 ∈ occ2]. *)
(** starting from a matching function mv, returns the new mv *)
let pat_subsumes
    (table : Symbols.table)
    (system : SE.fset)
    ?(mv : Match.Mvar.t = Match.Mvar.empty)
    (t1 : term) (pat2 : term pat) 
  : Match.Mvar.t option
  =
  let context = SE.reachability_context system in
  match Match.T.try_match ~mv table context t1 pat2
  with
  | FreeTyv | NoMatch _ -> None
  | Match mv -> Some mv


(** Auxiliary function to check if all instances of [o1] are instances of [o2]. *)
(** Returns the matching function, so that it can be reused for ext_occ_incl *)
let aux_occ_incl
    (conv : ('a, 'b) converter) 
    (table : Symbols.table)
    (system : SE.fset)
    ?(mv : Match.Mvar.t = Match.Mvar.empty)
    (o1 : ('a, 'b) simple_occ)
    (o2 : ('a, 'b) simple_occ)
  : Match.Mvar.t option =

  (* we ignore the subterm: it will be different, but doesn't matter *)
  (* we don't care about the variables bound above being the same, as we rename *)

  (* build a dummy term, which we use to match in one go many elements of
     the two occurrences *)
  (* TODO: there's no real reason to use boolean formulas, rather than just terms *)
  let mk_dummy (o:('a, 'b) simple_occ) : term =
    let phi_cnt = mk_eq ~simpl:false (conv.conv_cnt o.so_cnt) (conv.conv_cnt o.so_cnt) in
    let phi_coll = mk_eq ~simpl:false (conv.conv_cnt o.so_coll) (conv.conv_cnt o.so_coll) in
    (* usually when we use it there are no fv in coll, but it should still work *)
    let phi_ad = mk_eq ~simpl:false (conv.conv_ad o.so_ad) (conv.conv_ad o.so_ad) in
    Term.mk_ands ~simpl:false [phi_cnt; phi_coll; phi_ad]
  in
  let pat2 = Term.{
      pat_tyvars = [];
      pat_vars   = Vars.Sv.of_list o2.so_vars;
      pat_term   = mk_dummy o2;
    }
  in  

  let mv = pat_subsumes ~mv table system (mk_dummy o1) pat2 in
  match mv with
  | None -> None
  | Some mv -> (* only the condition is left to check. we want cond1 => cond2 *)
    (* start from the matching substitution [mv], and try to match all
       conditions of [o1.so_conds] with a condition of
       [o2.so_conds], updating [mv] along the way if successful. *)
    let mv = ref mv in

    let mk_cond2 cond2 = { pat2 with pat_term = cond2; } in
    let b = (* construct the inst. of cond2 on the fly, so maybe we get the wrong one and
               conclude it's not included. still fine, that's an overapproximation *)
      List.for_all (fun cond2 -> 
          List.exists (fun cond1 ->
              match 
                pat_subsumes ~mv:(!mv) table system cond1 (mk_cond2 cond2)
              with 
              | None -> false
              | Some mv' -> mv := mv'; true
            ) o1.so_cond
        ) o2.so_cond
    in
    if b then Some !mv else None



(** Inclusion for simple occurrences:
    checks if all instances of [o1] are instances of [o2] (ie [o2] subsumes [o1]). *)
(* let simple_occ_incl
    (conv : ('a, 'b) converter)
    (table : Symbols.table)
    (system : SE.fset)
    (o1 : ('a, 'b) simple_occ)
    (o2 : ('a, 'b) simple_occ)
  : bool =
  match aux_occ_incl conv table system o1 o2 with
    | Some _ -> true
    | None -> false
*)

(** Auxiliary function for timestamps inclusion:
    checks if all instances of [ts1] are instances of [ts2] (ie [ts2] subsumes [ts1]).
    Also returns the matching function. *)
(* not trivial, since for timestamps there is the case of predecessors *)
let aux_ts_occ_incl
    (table : Symbols.table)
    (system : SE.fset)
    ?(mv : Match.Mvar.t = Match.Mvar.empty)
    (ts1 : ts_occ)
    (ts2 : ts_occ)
  : Match.Mvar.t option =
  let f = aux_occ_incl ts_converter table system in
  match f ~mv ts1 ts2 with
  | Some mv -> Some mv
  | None -> f ~mv ts1 {ts2 with so_cnt = mk_pred ts2.so_cnt}
              (* if ts1 not incl in ts2, also try ts1 incl in pred(ts2) *)
              (* as "t <= pred(ts2) \/ t <= ts2" is the same as "t <= ts2" *)
              (* TODO read this carefully to make sure it does what we want *)
              

(** Inclusion for timestamp occurrences:
    Checks if all instances of [ts1] are instances of [ts2] (ie [ts2] subsumes [ts1]). *)
let ts_occ_incl
    (table : Symbols.table)
    (system : SE.fset)
    (ts1 : ts_occ) 
    (ts2 : ts_occ) 
  : bool =
  match aux_ts_occ_incl table system ts1 ts2 with
  | Some _ -> true
  | None -> false 



(** Inclusion for extended occurrences:
    Checks if all instances of [occ1] are instances of [occ2] (ie [occ2] subsumes [occ1]). *)
let ext_occ_incl
    (conv : ('a, 'b) converter)
    (table : Symbols.table)
    (system : SE.fset)
    (occ1 : ('a, 'b) ext_occ)
    (occ2 : ('a, 'b) ext_occ)
  : bool =
  let mv = aux_occ_incl conv table system occ1.eo_occ occ2.eo_occ in
  match mv with
  | None -> false
  | Some mv -> (* still have to check occ_type and source_ts *)
    (* we ignore the source itself: it's fine if it's different, as long as the timestamps are the same *)
    let mv =
      match occ1.eo_occtype, occ2.eo_occtype with
      | EI_direct, EI_direct -> Some mv
      | EI_indirect a1, EI_indirect a2 ->
        let pat2 = Term.{
            pat_tyvars = [];
            pat_vars   = Vars.Sv.of_list occ2.eo_occ.so_vars;
            pat_term   = a2;
          }
        in 
        pat_subsumes table system ~mv a1 pat2
      | _ -> None
    in
    match mv with
    | None -> false
    | Some mv ->
      let mv = ref mv in
      
      List.for_all (fun ts1 ->
          List.exists (fun ts2 ->
              match 
                aux_ts_occ_incl ~mv:(!mv) table system ts1 ts2
              with 
              | None -> false
              | Some mv' -> mv := mv'; true
            ) occ2.eo_source_ts
        ) occ1.eo_source_ts
        

(** Removes subsumed timestamps occurrences from a list *)
let clear_subsumed_ts
    (table : Symbols.table)
    (system : SE.fset)
    (occs : ts_occs) :
  ts_occs =
  List.clear_subsumed (ts_occ_incl table system) occs


(** Removes subsumed extended occurrences from a list *)
let clear_subsumed_occs
    (conv : ('a, 'b) converter)
    (table : Symbols.table)
    (system : SE.fset)
    (occs : ('a, 'b) ext_occ list) 
  : ('a, 'b) ext_occ list
  =
  List.clear_subsumed (ext_occ_incl conv table system) occs



(*------------------------------------------------------------------*)
(* Functions handling macro expansion in terms, when allowed *)

(* information used to check if a macro can be expanded in a term:
   - a tag indicating whether the occurrence is direct or indirect
     (for an indirect occurrence, the action producing it is recorded)
   - the trace context *)
type expand_info = occ_type * Constr.trace_cntxt


(** Expands t (not recursively) if it is a macro
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


(** Expands t as much as possible, recursively
    (only at toplevel, not in subterms) *)
let rec expand_macro_check_all (info:expand_info) (t:term) : term =
  match expand_macro_check_once info t with
  | Some t' -> expand_macro_check_all info t'
  | None -> t




(*------------------------------------------------------------------*)
(* Functions to find all timestamps occurring in a term *)
(** Gathers all timestamps at which macros occur in a term. *)
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
          let occ = {
              so_cnt  = ts;
              so_coll = mk_false; (* unused, so always set to false *)
              so_ad = (); (* unused *)
              so_vars = List.rev fv;
              so_cond = cond;
              so_subterm = mk_false} (* unused *)
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

type n_occ = (nsymb, unit) simple_occ
type n_occs = n_occ list

type name_occ = (nsymb, unit) ext_occ
type name_occs = name_occ list

(** Constructs a name occurrence *)
let mk_nocc (n:nsymb) (ncoll:nsymb) (fv:Vars.vars) (cond:terms) (st:term) : n_occ =
  mk_simple_occ n ncoll () fv cond st


(** Removes from occs all occurrences subsumed by another *)
let clear_subsumed_nameoccs 
    (table : Symbols.table)
    (system : SE.fset)
    (occs : name_occs)
  : name_occs =
  clear_subsumed_occs name_converter table system occs


(** Internally used to print a description of the occurrence *)
let pp_internal (ppf:Format.formatter) (occ:name_occ) : unit =
  let o = occ.eo_occ in
  match occ.eo_occtype with
  | EI_indirect a ->
    Fmt.pf ppf
      "%a @,(collision with %a)@ in action %a@ @[<hov 2>in term@ @[%a@]@]"
      Term.pp_nsymb o.so_cnt 
      Term.pp_nsymb o.so_coll
      Term.pp a
      Term.pp o.so_subterm
  | EI_direct ->
    Fmt.pf ppf
      "%a @,(collision with %a)@ @[<hov 2>in term@ @[%a@]@]"
      Term.pp_nsymb o.so_cnt
      Term.pp_nsymb o.so_coll
      Term.pp o.so_subterm

(** Prints a description of the occurrence *)
let pp (ppf:Format.formatter) (occ:name_occ) : unit =
  Printer.pr "  @[<hv 2>%a@]@;@;" pp_internal occ



(*------------------------------------------------------------------*)
(* Functions to look for illegal name occurrences in a term *)

(** Type of a function that takes a term, and generates a list of name occurrences in it.
    Also returns a list of ('a, 'b) simple occurrences, used to record
    information gathered during the exploration of the term
    (typically collisions between other things than names, but with the 'b so_ad field,
    can record anything useful).
    Uses
    - a continuation unit -> n_occs * 'a, 'b simple_occs
       when it does not want to handle the term it's given,
       and just asks to be called again on the subterms
    - a continuation fv -> cond -> p -> se -> st -> term -> n_occs * ('a,'b) simple_occs,
       that calls the function again on the given parameters,
       for when it needs to do finer things
       (typically handle some of the subterms manually, and call this continuation
          on the remaining ones,
        or handle subterms at depth 1 by hand, and call the continuation on subterms at depth 2).
      Functions of this type don't need to unfold macros, that's handled separately. *)
type ('a, 'b) f_fold_occs = 
  (unit -> n_occs * ('a, 'b) simple_occs) -> (* continuation: give up and try again on subterms *)
  (fv:Vars.vars ->       (* continuation: to be called on strict subterms (for rec calls) *)
   cond:terms ->
   p:MP.pos ->           
   info:expand_info ->
   st:term ->
   term ->
   n_occs * ('a, 'b) simple_occs)->         
  info:expand_info ->  (* info to expand macros, incl. system at current pos *)
  fv:Vars.vars ->      (* variables bound above the current position *)
  cond:terms ->        (* condition at the current position *)
  p:MP.pos ->          (* current position*)
  st:term ->           (* a subterm we're currently in (for printing purposes) *)
  term ->              (* term at the current position *)
  n_occs * ('a, 'b) simple_occs (* found name occurrences, and other occurrences *)


(** given a f_fold_occs function get_bad_occs,
    calls get_bad_occs, is called again when get_bad_occs asks
    for recursive calls on subterms, and handles the case where
    get_bad_occs calls its first continuation (ie gives up)
    by 1) unfolding the term, if it's a macro that can be unfolded
       2) doing nothing, if it's a macro that can't be unfolded
          (in that case, fold_macro_support will generate a separate iocc 
          for that)
       3) using Match.Pos.fold_shallow, to recurse on subterms at depth 1. *)
let fold_bad_occs
    (get_bad_occs: ('a, 'b) f_fold_occs)
    ~(fv:Vars.vars)
    (info:expand_info)
    (t:term) : n_occs * ('a, 'b) simple_occs
  =
  let rec get
      ~(fv:Vars.vars) ~(cond:Term.terms) ~(p:MP.pos) ~(info:expand_info)
      ~(st:Term.term) 
      (t:term) : n_occs * ('a, 'b) simple_occs
    =
    let typ, contx = info in
    let se = SE.to_arbitrary contx.system in
    (* the continuation to be passed to get_bad_occs for cases it does 
       not handle *)
    let retry_on_subterms () : n_occs * ('a, 'b) simple_occs =
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
(** given a function find_occs that generates a list of occurrences found in a term,
     expanding macros when possible according to expand_info but
     not otherwise (undef and maybedef macros will be handled by 
     fold_macro_support);
    computes the list of all occurrences in the list of source terms.
    Relies on fold_macro_support to look through all macros in the term. *)
let find_occurrences
    ?(pp_ns: (unit Fmt.t) option=None)
    (conv : ('a, 'b) converter)
    (find_occs : 
       (fv:Vars.vars ->
        expand_info ->
        term ->
        n_occs * ('a, 'b) simple_occs))
    (contx : Constr.trace_cntxt)
    (env : Vars.env)
    (sources : terms) : name_occs * ('a, 'b) ext_occs
  =
  let system = contx.system in
  let table = contx.table in

  let ppp ppf () = match pp_ns with
    | Some x -> Fmt.pf ppf "of %a " x ()
    | None   -> Fmt.pf ppf ""
  in

  (* TODO: we currently print info only on the name occurrences. 
     we could print some for the 'a, 'b ext_occs, would that be useful? *)
  (* direct occurrences *)
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
         (* add the info to the occurrences *)
         let occs = List.map (fun o -> {eo_occ=o; eo_occtype=EI_direct; eo_source=[t]; eo_source_ts=ts}) noccs in
         let acc = List.map (fun o -> {eo_occ=o; eo_occtype=EI_direct; eo_source=[t]; eo_source_ts=ts}) acc in
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
        (* todo: we could print which source the indirect occs came from,
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
        let occs = List.map (fun o -> {eo_occ=o; eo_occtype=(EI_indirect a); eo_source=src; eo_source_ts=ts}) noccs in
        let acc = List.map (fun o -> {eo_occ=o; eo_occtype=(EI_indirect a); eo_source=src; eo_source_ts=ts}) acc in
        ind_occs @ occs, ind_acc @ acc)
      contx env sources ([], [])
  in

  (* printing *)
  List.iter (Printer.pr "%a" pp) ind_occs;
  if ind_occs = [] then
    Printer.pr "  (no occurrences)@;";

  (* remove subsumed occs *)
  let occs = dir_occs @ ind_occs in
  let acc = dir_acc @ ind_acc in
  let loccs = List.length occs in

  (* todo: this would need to change if the system depends on the occ *)
  let occs = clear_subsumed_nameoccs table system occs in
  let acc = clear_subsumed_occs conv table system acc in
  let loccs' = List.length occs in
  let lsub = loccs - loccs' in

  Printer.pr "@;Total: @[<v 0>%d bad occurrence%s@;" loccs (if loccs = 1 then "" else "s");
  Printer.pr "%d of them %s subsumed by another@;" lsub (if lsub = 1 then "is" else "are");
  Printer.pr "%d bad occurrence%s remaining@;@]@;" loccs' (if loccs' = 1 then "" else "s");
  occs, acc




(** Given a f_fold_occs,
   computes the list of all occurrences in sources,
   taking care of macro expansion and going through all terms,
   using fold_macro_support and map_fold *)   
let find_all_occurrences
    ?(pp_ns: (unit Fmt.t) option=None)
    (conv : ('a, 'b) converter)
    (get_bad_occs: ('a, 'b) f_fold_occs)
    (contx : Constr.trace_cntxt)
    (env : Vars.env)
    (sources : terms) : name_occs * ('a, 'b) ext_occs
  =
  find_occurrences ~pp_ns conv (fold_bad_occs get_bad_occs) contx env sources



(** Interprets phi as phi_1 /\ … /\ phi_n,
    keeps all phi_i of the form i = j where
    i is a free variable and not j (or conversely),
    and returns the substitution mapping such i's to the corresponding j
    (or j to i if j is free) *)
(* note that this may introduce several mappings for the same i, only one will
   actually be used when applying the substitution, which is fine. *)
let find_equalities
  (fv : Vars.vars)
  (phi : term)
  : subst =
  let phis = decompose_ands phi in
  List.filter_map (fun x -> x)
    (List.map
       (fun t ->
          match destr_eq t with
          | Some (Var u, Var v) when List.mem u fv && not (List.mem v fv) ->
            Some (ESubst (mk_var u, mk_var v))
          | Some (Var v, Var u) when List.mem u fv && not (List.mem v fv) ->
            Some (ESubst (mk_var u, mk_var v))
          | _ -> None)
       phis)
  

(** Interprets phi as phi_1 /\ … /\ phi_n,
    and reconstructs it to simplify trivial equalities *)
let clear_trivial_equalities (phi : term) : term =
  let phis = decompose_ands phi in
  let phis =
    List.filter_map (fun x -> x)
      (List.map
         (fun t ->
            match destr_eq t with
            | Some (u, v) when u = v -> None
            | _ -> Some t)
         phis)
  in
  mk_ands ~simpl:true phis



(** Type of a function generating a formula meant to say
    "the occurrence is actually a collision" (or its negation) *)
type ('a, 'b) occ_formula =
  negate:bool -> 'a -> 'a -> 'b -> term

(** occ_formula for name occurrences *)
let name_occ_formula
    ~(negate : bool)
    (n : nsymb)
    (ncoll : nsymb)
    () : term =
  if not negate then
    mk_indices_eq ~simpl:true ncoll.s_indices n.s_indices
  else
    mk_indices_neq ~simpl:false ncoll.s_indices n.s_indices
  

(** Dummy occ_formula for empty occurrences *)
let empty_occ_formula
    ~(negate : bool)
    ()
    ()
    () 
  : term =
  mk_false

(*------------------------------------------------------------------*)
(* Proof obligations for a name occurrence *)

(** Constructs the formula
    "exists free vars.
      (exists t1.occ_vars. action ≤ t1.occ_cnt || 
       … || 
       exists tn.occ_vars. action ≤ tn.occ_cnt) &&
      conditions of occ && 
      the occ is a collision" (this last part produced by phiocc)
    which will be the condition of the proof obligation when finding the occurrence occ.
    action is the action producing the occ (when indirect). ts=[t1, …, tn] are the timestamp occurrences in t.
    The free vars of occ.occ_cnt, action, and cond not bound in the sequent's env should be in occ.occ_vars,
    which is the case if occ was produced correctly
    (ie by Match.fold given either empty (for direct occurrences)
     or iocc_vars (for indirect occurrences).
    The free vars of ts should be all be bound in the sequent's env.
    If negate is set to true, returns instead the negation of that formula. *)
let occurrence_formula
    ~(negate : bool)
    (phiocc : ('a, 'b) occ_formula) 
    (occ : ('a, 'b) ext_occ)
  : term
  =
  let o = occ.eo_occ in
  let fv = o.so_vars in
  let ts = occ.eo_source_ts in
  let cond = o.so_cond in

  (* the formula "cnt is a collision" (or its negation) *)
  let phi_cnt = phiocc ~negate o.so_cnt o.so_coll o.so_ad in

  (* get in phi_cnt the equalities forcing certain vars of the occ to be equal to not free vars *)
  let sigma = find_equalities fv phi_cnt in

  (* we apply this substitution in the formula we generate.
     Produces logically equivalent, but simpler, formulas. *)
  (* the equality formula is still needed, as eg if it contains (i' = i /\ i' = j)
     we still need to remember that j = i' = i. *)
  let sub t = subst sigma t in
  let phi_cnt = sub phi_cnt in
  let phi_cnt = clear_trivial_equalities phi_cnt in
  let cond = List.map sub cond in

  let phi_cond_cnt =
    if not negate then
      mk_ands ~simpl:true (cond @ [phi_cnt])
    else
      mk_impl ~simpl:true (mk_ands ~simpl:true cond) phi_cnt
  in 

  match occ.eo_occtype with
  | EI_indirect a ->
    (* indirect occurrence: we also generate the timestamp inequalities *)
    let a = sub a in
    (* no need to substitute ts. *)
    (* all variables in ts are quantified existentially, so they cannot be the renamed variables. *)
    (* imprecise: they could initially have been the same as vars in the occ, but we forgot it.
       if we want to improve that, we'd need to only ex quantify the vars in ts not bound in the occ,
       but that's tricky, as it also means these vars can't be used to unify when subsuming timestamps *)
    let phis_time =
      List.map (fun (ti:ts_occ) ->
          mk_exists ~simpl:true
            ti.so_vars
            (mk_ands ~simpl:true ((mk_timestamp_leq a ti.so_cnt)::ti.so_cond))
        ) ts
    in
    let phi_time = mk_ors ~simpl:true phis_time in

    if not negate then
      mk_exists ~simpl:true fv (mk_and ~simpl:true phi_time phi_cond_cnt)
    else
      mk_forall ~simpl:true fv (mk_impl ~simpl:true phi_time phi_cond_cnt)

  | EI_direct -> (* direct occurrence *)
    if not negate then
      mk_exists ~simpl:true fv phi_cond_cnt
    else
      mk_forall ~simpl:true fv phi_cond_cnt


(** occurrence formula for names *)
let name_occurrence_formula = occurrence_formula name_occ_formula


(*------------------------------------------------------------------*)
(* Proof obligations for name occurrences *)



(** variant of occurrence_formula that returns
    all found occurrences as well as the formulas,
    for more complex use cases (eg intctxt) *)
let occurrence_formulas_with_occs
    ?(negate : bool=false)
    ?(pp_ns: (unit Fmt.t) option=None)
    (conv : ('a, 'b) converter)
    (phi_acc : ('a, 'b) occ_formula)
    (get_bad_occs: ('a, 'b) f_fold_occs)
    (contx : Constr.trace_cntxt)
    (env : Vars.env)
    (sources : terms)
  : terms * terms * name_occs * ('a, 'b) ext_occs
  =
  let occs, accs = find_all_occurrences ~pp_ns conv get_bad_occs contx env sources in
  let foccs = List.map (name_occurrence_formula ~negate) occs in
  let faccs = List.map (occurrence_formula ~negate phi_acc) accs in
  (foccs, faccs, occs, accs)


(** given
   - a f_fold_occs function (see above)
   - a context (in particular, that includes the systems we want to use)
   - the environment
   - a list of sources where we search for occurrences
   - conversion (for detecting duplicate) and formula functions for 'a, 'b occurrences
   - optionally, a pp_ns that prints what we look for (just for pretty printing)
   
   computes two list of formulas whose disjunctions respectively mean
   "a bad name occurrence happens" and "an 'a, 'b occurrence is a collision"
      (or, alternatively, if negate is set to true,
   whose conjunction means "no bad occurrence happens" and "no collision happens") *)
let occurrence_formulas
    ?(negate : bool=false)
    ?(pp_ns: (unit Fmt.t) option=None)
    (conv : ('a, 'b) converter)
    (phi_acc : ('a, 'b) occ_formula)
    (get_bad_occs: ('a, 'b) f_fold_occs)
    (contx : Constr.trace_cntxt)
    (env : Vars.env)
    (sources : terms)
  : terms * terms
  =
  let (occs, accs, _, _) =
    occurrence_formulas_with_occs
      ~negate ~pp_ns conv phi_acc
      get_bad_occs contx env sources
  in
  (occs, accs)

 
(** occurrence_formula instantiated for the case where we only look for names *)
(** eg fresh *)
let name_occurrence_formulas
    ?(negate : bool=false)
    ?(pp_ns: (unit Fmt.t) option=None)
    (get_bad_occs: (unit, unit) f_fold_occs)
    (contx : Constr.trace_cntxt)
    (env : Vars.env)
    (sources : terms)
  : terms =  
  let (occs, _) =
    occurrence_formulas
      ~negate ~pp_ns empty_converter empty_occ_formula
      get_bad_occs contx env sources
  in
  occs

