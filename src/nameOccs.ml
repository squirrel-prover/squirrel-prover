open Utils

module MP = Match.Pos
module SE = SystemExpr

module PathCond = Iter.PathCond

(*------------------------------------------------------------------*)

module Name = struct
  (** An applied named [symb(args)] *)
  type t = { symb : Term.nsymb; args : Term.terms; }

  let subst (s : Term.subst) (n : t) : t =
    { n with args = List.map (Term.subst s) n.args }

  let pp fmt (n : t) =
    if n.args = [] then
      Fmt.pf fmt "%a" Symbols.pp n.symb.s_symb
    else
      Fmt.pf fmt "%a(%a)"
        Symbols.pp n.symb.s_symb
        (Fmt.list ~sep:Fmt.comma Term.pp) n.args

  let of_term : Term.term -> t = function
    | Name (symb, args) -> { symb; args; }
    | _ -> assert false

  let to_term { symb; args; } = Term.mk_name symb args

  (** looks for a name with the same symbol in the list *)
  let exists_name (n:t) (ns:t list) : bool =
    List.exists (fun nn -> n.symb.s_symb = nn.symb.s_symb) ns

  (** finds all names with the same symbol in the list *)
  let find_name (n:t) (ns:t list) : t list =
    List.filter (fun nn -> n.symb.s_symb = nn.symb.s_symb) ns
end

(*------------------------------------------------------------------*)

type occ_type =
  | EI_direct
  | EI_indirect of Term.term

let subst_occtype (sigma : Term.subst) (ot : occ_type) : occ_type =
  match ot with
  | EI_direct -> EI_direct
  | EI_indirect a -> EI_indirect (Term.subst sigma a)

(* Remarks:
   - We could store a position in the term where the occ was, as in Iter.occ,
     but we don't use it anywhere for now
   - We could store the fset at the point where the occ was found, which would
     be more precise (we would need to prove the goal for the occ only in that
     fset). Since fold_macro_support does not give us the fset where the iocc
     is, we would still potentially be a little imprecise.
     We'll see if that's an issue later, for now we don't do that. *)
type ('a, 'b) simple_occ =
  {so_cnt     : 'a;
   so_coll    : 'a;
   so_ad      : 'b;
   so_vars    : Vars.vars;
   so_cond    : Term.terms;
   so_occtype : occ_type;
   so_subterm : Term.term;
  }

type ('a, 'b) simple_occs = (('a, 'b) simple_occ) list

let mk_simple_occ
    (cnt : 'a) (coll : 'a) (ad : 'b)
    (vars : Vars.vars) (cond : Term.terms) (ot : occ_type) (st : Term.term)
  : ('a, 'b) simple_occ 
  =
  {so_cnt=cnt; so_coll=coll; so_ad=ad; so_vars=vars;
   so_cond=cond; so_occtype=ot; so_subterm=st}

type ts_occ = (Term.term, unit) simple_occ
type ts_occs = ts_occ list

type empty_occ = (unit, unit) simple_occ
type empty_occs = empty_occ list


(*------------------------------------------------------------------*)
(** Type of a function generating a formula meant to say
    "the occurrence is actually a collision" (or its negation) *)
(** we also use this formula to compute occurrence subsumption
     (if o1 generates a particular case of o2 then it is subsumed) *)
type ('a, 'b) occ_formula =
  negate:bool -> 'a -> 'a -> 'b -> Term.term

(** [occ_formula] for name occurrences *)
let name_occ_formula
    ~(negate : bool)
    (n       : Name.t)
    (ncoll   : Name.t)
    ()
  : Term.term
  =
  (* sanity check: only apply when same symbol *)
  assert (n.symb = ncoll.symb);
  if not negate then
    Term.mk_eqs ~simpl:true ncoll.args n.args
  else
    Term.mk_neqs ~simpl:false ncoll.args n.args

(** occ_formula for timestamp occurrences *)
let ts_occ_formula
    ~(negate : bool)
    (ts  : Term.term)
    (tss : Term.term)
    () 
  : Term.term 
  =
  if not negate then
    Term.mk_eq ~simpl:true ts tss
  else
    Term.mk_not ~simpl:false (Term.mk_eq ~simpl:false ts tss)


(** Dummy occ_formula for empty occurrences *)
let[@warning "-27"] empty_occ_formula
    ~(negate : bool)
    ()
    ()
    ()
  : Term.term =
  Term.mk_false

(*------------------------------------------------------------------*)
(** See `.mli` *)
type ('a, 'b) ext_occ = {
  eo_occ       : ('a, 'b) simple_occ;
  eo_source    : Term.terms; 
  eo_source_ts : ts_occs;
  
  eo_path_cond : Iter.PathCond.t;
}

type ('a, 'b) ext_occs = (('a, 'b) ext_occ) list

(*------------------------------------------------------------------*)
(** Occurrence subsumption/inclusion *)
(** occ1 included in occ2 MUST mean that
    (occ1 is a collision) \/ (occ2 is a collision) <=> (occ2 is a collision) *)
(** so that we only need to look at occ2 *)
(** ie occ1 is an instance of occ2, in an instance of its action,
    with a STRONGER condition *)
(** (not weaker!!) *)


(** Checks if [t1] is included in the patterm [pat2], i.e. [t1 ∈ occ2]. *)
(** starting from a matching function mv, returns the new mv *)
let pat_subsumes
    (table : Symbols.table)
    (system : SE.fset)
    ?(mv : Match.Mvar.t = Match.Mvar.empty)
    (t1 : Term.term) (pat2 : Term.term Term.pat)
  : Match.Mvar.t option
  =
  let context = SE.reachability_context system in
  match Match.T.try_match ~mv table context t1 pat2
  with
  | FreeTyv | NoMatch _ -> None
  | Match mv -> Some mv


(** Auxiliary function to check if all instances of [o1]
    are instances of [o2]. *)
(** Returns the matching function, so that it can be reused for ext_occ_incl *)
(** we use the occ_formula to turn 'a, 'b into a term.
    this means we subsume occurrences that are not actually equal
    as long as they produce the same formula in the end.
    In principle it should be fine, if not just give
    a different occ_formula that doesn't simplify anything. *)
let aux_occ_incl
    (conv : ('a, 'b) occ_formula)
    (table : Symbols.table)
    (system : SE.fset)
    ?(mv : Match.Mvar.t = Match.Mvar.empty)
    (o1 : ('a, 'b) simple_occ)
    (o2 : ('a, 'b) simple_occ)
  : Match.Mvar.t option =

  (* we ignore the subterm: it will be different, but doesn't matter *)
  (* we don't care about the variables bound above being the same,
     as we rename *)

  (* build a dummy term, which we use to match in one go many elements of
     the two occurrences *)
  (* TODO: there's no real reason to use boolean formulas,
     rather than just terms *)
  let mk_dummy (o : ('a, 'b) simple_occ) : Term.term =
    let phi_f = conv ~negate:false o.so_cnt o.so_coll o.so_ad in
    (* usually when we use it there are no fv in coll,
       but it should still work *)
    let phi_ac = match o.so_occtype with
        | EI_direct -> Term.mk_eq ~simpl:false Term.mk_false Term.mk_false
        | EI_indirect a -> Term.mk_eq ~simpl:false a a
    in
    Term.mk_ands ~simpl:false [phi_f; phi_ac]
  in
  let pat2 = Term.{
      pat_tyvars = [];
      pat_vars   = Vars.Tag.local_vars o2.so_vars;
      (* local information, since we allow to match diff operators *)
      
      pat_term   = mk_dummy o2;
    }
  in

  let mv = pat_subsumes ~mv table system (mk_dummy o1) pat2 in
  match mv with
  | None -> None
  | Some mv -> (* only the condition is left to check.
                  we want cond1 => cond2 *)
    (* start from the matching substitution [mv], and try to match all
       conditions of [o1.so_conds] with a condition of
       [o2.so_conds], updating [mv] along the way if successful. *)
    let mv = ref mv in

    let mk_cond2 cond2 = { pat2 with pat_term = cond2; } in
    let b = (* construct the inst. of cond2 on the fly,
               so maybe we get the wrong one and
               conclude it's not included.
               still fine, that's an overapproximation *)
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
  let f = aux_occ_incl ts_occ_formula table system in
  match f ~mv ts1 ts2 with
  | Some mv -> Some mv
  | None -> f ~mv ts1 {ts2 with so_cnt = Term.mk_pred ts2.so_cnt}
              (* if ts1 not incl in ts2, also try ts1 incl in pred(ts2) *)
              (* as "t <= pred(ts2) \/ t <= ts2" is the same as "t <= ts2" *)
              (* TODO read this carefully to make sure it does what we want *)


(** Inclusion for timestamp occurrences:
    Checks if all instances of [ts1] are instances of [ts2]
    (ie [ts2] subsumes [ts1]). *)
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
    Checks if all instances of [occ1] are instances of [occ2]
    (ie [occ2] subsumes [occ1]). *)
let ext_occ_incl
    (conv : ('a, 'b) occ_formula)
    (table : Symbols.table)
    (system : SE.fset)
    (occ1 : ('a, 'b) ext_occ)
    (occ2 : ('a, 'b) ext_occ)
  : bool 
  =
  let mv = aux_occ_incl conv table system occ1.eo_occ occ2.eo_occ in
  match mv with
  | None -> false
  | Some mv -> (* still have to check [eo_path_cond], [occ_type] and [source_ts] *)
    let mv = ref mv in
    (* path condition inclusion:
       path conditions have no free variables, hence we do not 
       need to forward [mv] to it. *)
    PathCond.incl occ1.eo_path_cond occ2.eo_path_cond &&

    (* source timestamps inclusion *)
    (* we ignore the source itself: it's fine if it's different,
       as long as the timestamps are the same *)
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
    (conv : ('a, 'b) occ_formula)
    (table : Symbols.table)
    (system : SE.fset)
    (occs : ('a, 'b) ext_occ list)
  : ('a, 'b) ext_occ list
  =
  List.clear_subsumed (ext_occ_incl conv table system) occs


(*------------------------------------------------------------------*)
(* Functions handling macro expansion in terms, when allowed *)

type expand_info = occ_type * Constr.trace_cntxt

let expand_macro_check_once
    ((ot, c):expand_info) (t : Term.term) : Term.term option 
  =
  match t with
  | Macro (m, l, ts) ->
    if match ot with
      | EI_direct ->
        begin
          match c.models with
          | Some m -> Constr.query ~precise:true m [`Pos, Happens ts]
          | None -> false
        end
      | EI_indirect _ -> true
      (* as long as we call on ioccs produced by fold_macro_support,
           invariant: expansion is always allowed *)
      (* we need to know that if a macro does not expand here,
          then it will be handled by another iocc *)
    then
      match Macros.get_definition c m ~args:l ~ts with
      | `Def t' -> Some t'
      | `Undef | `MaybeDef -> None
    else
      None
  | _ -> None

let rec expand_macro_check_all (info:expand_info) (t:Term.term) : Term.term =
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
  let _typ, contx = info in
  let system = contx.system in
  let se = (SE.reachability_context system).set in
  let rec get (t : Term.term)
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
              so_coll = Term.mk_false; (* unused, so always set to false *)
              so_ad = (); (* unused *)
              so_vars = List.rev fv;
              so_cond = cond;
              so_occtype = EI_direct;
              so_subterm = Term.mk_false} (* unused *)
          in
          [occ] @ 
          List.concat_map (fun t ->
              get ~fv ~cond ~p ~se t
            ) (ts :: l)
      end

    | _ ->
      MP.fold_shallow
        (fun t' se fv cond p occs ->
           occs @ (get t' ~fv ~cond ~p ~se))
        ~se ~fv ~p ~cond [] t
  in
  get t ~fv ~cond:[] ~p:MP.root ~se


(*------------------------------------------------------------------*)
(** Returns all timestamps occuring in macros in a list of terms.
    Should only be used when sources are directly occurring,
    not themselves produced by unfolding macros *)
let get_macro_actions
    (contx : Constr.trace_cntxt)
    (sources : Term.terms) : ts_occs
  =
  let ei = (EI_direct, contx) in
  let actions =
    List.concat_map (fun t -> get_actions_ext t ei) sources
  in
  let table = contx.table in
  let system = contx.system in
  clear_subsumed_ts table system actions


(*------------------------------------------------------------------*)
(** {2 Occurrence of a name} *)

type n_occ = (Name.t, unit) simple_occ
type n_occs = n_occ list

type name_occ = (Name.t, unit) ext_occ
type name_occs = name_occ list

(** Constructs a name occurrence. *)
(** we do not refresh ncoll's variables, ie it's assumed to be at toplevel *)
let mk_nocc
    (n : Name.t) (ncoll : Name.t) (fv : Vars.vars) (cond : Term.terms)
    (ot : occ_type) (st : Term.term) : n_occ
  =
  let fv, sigma = Term.refresh_vars fv in
  let n = Name.subst sigma n in
  let cond = List.map (Term.subst sigma) cond in
  let ot = subst_occtype sigma ot in
  mk_simple_occ n ncoll () fv cond ot st

(*------------------------------------------------------------------*)
(** Finds all names with the same symbol in the list, returns the
    corresponding n_occs *)
let find_name_occ
    (n:Name.t) (ns:Name.t list)
    (fv:Vars.vars) (cond:Term.terms) (ot:occ_type) (st:Term.term)
  : n_occs =
  List.map
    (fun (nn:Name.t) -> mk_nocc n nn fv cond ot st)
    (Name.find_name n ns)
    
(*------------------------------------------------------------------*)
(** Removes from occs all occurrences subsumed by another *)
let clear_subsumed_nameoccs
    (table : Symbols.table)
    (system : SE.fset)
    (occs : name_occs)
  : name_occs =
  clear_subsumed_occs name_occ_formula table system occs

(*------------------------------------------------------------------*)
(** Internally used to print a description of the occurrence *)
let pp_internal (ppf:Format.formatter) (occ:name_occ) : unit =
  let o = occ.eo_occ in
  match o.so_occtype with
  | EI_indirect a ->
    Fmt.pf ppf
      "@[%a@] @,(collision with @[%a@])@ in action @[%a@]@ @[<hov 2>in term@ @[%a@]@]"
      Name.pp o.so_cnt
      Name.pp o.so_coll
      Term.pp a
      Term.pp o.so_subterm
  | EI_direct ->
    Fmt.pf ppf
      "@[%a@] @,(collision with @[%a@])@ @[<hov 2>in term@ @[%a@]@]"
      Name.pp o.so_cnt
      Name.pp o.so_coll
      Term.pp o.so_subterm

(** Prints a description of the occurrence *)
let pp_name_occ (fmt:Format.formatter) (occ:name_occ) : unit =
  Fmt.pf fmt "@[<hv 2>%a@]" pp_internal occ

let pp_name_occs (fmt:Format.formatter) (occs:name_occ list) : unit =
  if occs = [] then
    Fmt.pf fmt "(no occurrences)@;"
  else
    Fmt.list ~sep:(Fmt.any "@;@;") pp_name_occ fmt occs

(*------------------------------------------------------------------*)
(** {2 Functions to look for illegal name occurrences in a term} *)

type ('a, 'b) f_fold_occs =
  (unit -> n_occs * ('a, 'b) simple_occs) ->
  (fv:Vars.vars ->
   cond:Term.terms ->
   p:MP.pos ->
   info:expand_info ->
   st:Term.term ->
   Term.term ->
   n_occs * ('a, 'b) simple_occs)->
  info:expand_info ->
  fv:Vars.vars ->
  cond:Term.terms ->
  p:MP.pos ->
  st:Term.term ->
  Term.term ->
  n_occs * ('a, 'b) simple_occs


(*------------------------------------------------------------------*)
(** Given a [f_fold_occs] function [get_bad_occs],
    calls [get_bad_occs], is called again when [get_bad_occs] asks
    for recursive calls on subterms, and handles the case where
    get_bad_occs calls its first continuation (ie gives up)
    by 1) unfolding the term, if it's a macro that can be unfolded
       2) doing nothing, if it's a macro that can't be unfolded
          (in that case, fold_macro_support will generate a separate iocc
          for that)
       3) using [Match.Pos.fold_shallow], to recurse on subterms at depth 1. *)
let fold_bad_occs
    (get_bad_occs : ('a, 'b) f_fold_occs)
    ~(fv          : Vars.vars)
    (info         : expand_info)
    (t            : Term.term) 
  : n_occs * ('a, 'b) simple_occs
  =
  let rec get
      ~(fv:Vars.vars) ~(cond:Term.terms) ~(p:MP.pos) ~(info:expand_info)
      ~(st:Term.term)
      (t:Term.term) : n_occs * ('a, 'b) simple_occs
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
             let sst = if Term.is_binder t then t' else st in
             let (newoccs, newacc) = get t' ~fv ~cond ~p ~info ~st:sst in
             (occs @ newoccs, acc @ newacc))
          ~se ~fv ~p ~cond ([], []) t
    in
    get_bad_occs retry_on_subterms get ~info ~fv ~cond ~p ~st t
  in
  get ~fv ~cond:[] ~p:MP.root ~info ~st:t t


(*------------------------------------------------------------------*)
(** Internal.
    Given a function find_occs that generates a list of occurrences
    found in a term,
    expanding macros when possible according to expand_info but
    not otherwise (undef and maybedef macros will be handled by
    fold_macro_support);
    computes the list of all occurrences in the list of source terms.
    Relies on fold_macro_support to look through all macros in the term. *)
let find_occurrences
    ~(mode : Iter.allowed_constants)   (* allowed sub-terms without further checks *)
    ?(pp_ns    : unit Fmt.t option = None)
    (conv      : ('a, 'b) occ_formula)
    (find_occs :
       (fv : Vars.vars ->
        expand_info    ->
        Term.term      ->
        n_occs * ('a, 'b) simple_occs))
    (contx     : Constr.trace_cntxt)
    (env       : Env.t)
    (sources   : Term.terms) 
  : name_occs * ('a, 'b) ext_occs
  =
  let system = contx.system in
  let table = contx.table in

  let ppp ppf = match pp_ns with
    | Some x -> Fmt.pf ppf "of @[%a@] " x ()
    | None   -> Fmt.pf ppf ""
  in

  (* TODO: we currently print info only on the name occurrences.
     we could print some for the 'a, 'b ext_occs, would that be useful? *)
  if pp_ns <> None then Printer.pr "@[<v 0>";
  (* direct occurrences *)
  let dir_occs, dir_acc =
    List.fold_left
      (fun (dir_occs, dir_acc) t -> (* find direct occurrences in t *)
         (* timestamps occurring in t *)
         let ts = get_macro_actions contx [t] in
         (* name occurrences in t *)
         let noccs, acc = find_occs ~fv:[] (EI_direct, contx) t in
         (* add the info to the occurrences *)
         let occs = 
           List.map
             (fun o -> {eo_occ=o; eo_source=[t]; eo_source_ts=ts; eo_path_cond = Iter.PathCond.Top; }) 
             noccs
         in
         let acc = 
           List.map
             (fun o -> {eo_occ=o; eo_source=[t]; eo_source_ts=ts; eo_path_cond = Iter.PathCond.Top; }) 
             acc
         in

         (* printing *)
         if pp_ns <> None && occs <> [] then
           Printer.pr "@[<hv 2>\
                       @[<hov 0>Direct bad occurrences@ @[%t@]in@ @[%a@]:@]\
                       @;@[%a@]@]@;@;@;"
             ppp Term.pp t pp_name_occs occs;
         dir_occs @ occs, dir_acc @ acc)
      ([], [])
      sources
  in

  (* indirect occurrences *)
  let ind_occs, ind_acc =
    Iter.fold_macro_support ~mode (fun iocc (ind_occs, ind_acc) ->
        (* todo: if fold_macro_support stored in iocc the fset
           for the place where the iocc was found, we could give it
           instead of contx to find_occs *)
        (* todo: we could print which source the indirect occs came from,
           not sure that's useful though *)
        let t = iocc.iocc_cnt in
        let sfv = iocc.iocc_vars in
        let src = iocc.iocc_sources in
        let a =
          Term.mk_action iocc.iocc_aname (Action.get_args iocc.iocc_action)
        in
        (* a's free variables should always be in fv \cup env *)
        assert (Vars.Sv.subset
                  (Term.fv a)
                  (Vars.Sv.union sfv (Vars.to_vars_set env.vars)));
        (* timestamps occurring in sources *)
        let ts = get_macro_actions contx src in
        (* indirect occurrences in iocc *)
        let noccs, acc =
          find_occs ~fv:(Vars.Sv.elements sfv) (EI_indirect a, contx) t
        in
        (* add the info *)
        let occs = 
          List.map
            (fun o -> 
               { eo_occ       = o; 
                 eo_source    = src; 
                 eo_source_ts = ts; 
                 eo_path_cond = iocc.iocc_path_cond; }
            ) noccs
        in
        let acc = 
          List.map
            (fun o -> 
               {eo_occ       = o;
                eo_source    = src; 
                eo_source_ts = ts; 
                eo_path_cond = iocc.iocc_path_cond; }
            ) acc
        in
        ind_occs @ occs, ind_acc @ acc)
      contx env sources ([], [])
  in
  
  (* printing *)
  if pp_ns <> None && ind_occs <> [] then
    Printer.pr "@[<hv 2>@[Bad occurrences@ @[%t@]in other actions:@]@;%a@]@;@;"
      ppp
      pp_name_occs ind_occs;

  (* remove subsumed occs *)
  let occs = dir_occs @ ind_occs in
  let acc = dir_acc @ ind_acc in
  let loccs = List.length occs in

  (* todo: this would need to change if the system depends on the occ *)
  let occs = clear_subsumed_nameoccs table system occs in
  let acc = clear_subsumed_occs conv table system acc in
  let loccs' = List.length occs in
  let lsub = loccs - loccs' in

  if pp_ns <> None && loccs <> 0 then
    (Printer.pr
       "Total: @[<v 0>%d bad occurrence%s@;"
       loccs (if loccs = 1 then "" else "s");
     Printer.pr
       "%d of them %s subsumed by another@;"
       lsub (if lsub = 1 then "is" else "are");
     Printer.pr
       "%d bad occurrence%s remaining@;@]"
       loccs' (if loccs' = 1 then "" else "s"));
  if pp_ns <> None then
    Printer.pr "@]";
  occs, acc

(*------------------------------------------------------------------*)
(** Internal. 
    Given a [f_fold_occs],
    computes the list of all occurrences in sources,
    taking care of macro expansion and going through all terms,
    using [fold_macro_support] and [map_fold] *)
let find_all_occurrences
    ~(mode : Iter.allowed_constants)   (* allowed sub-terms without further checks *)
    ?(pp_ns       : (unit Fmt.t) option=None)
    (conv         : ('a, 'b) occ_formula)
    (get_bad_occs : ('a, 'b) f_fold_occs)
    (contx        : Constr.trace_cntxt)
    (env          : Env.t)
    (sources      : Term.terms) 
  : name_occs * ('a, 'b) ext_occs
  =
  find_occurrences ~mode ~pp_ns conv (fold_bad_occs get_bad_occs) contx env sources

(*------------------------------------------------------------------*)
(** {2 Utilities to build the proof-obligations} *)

(** Internal.
    Saturates a substitution sigma.
    ie returns sigma' = [u1 -> v1, …, un -> vn] such that
    - forall i <> i'. ui <> ui'
    - forall i, j. ui <> vj
    - for all term t, t sigma is equal to t modulo the equalities ui = vi
    - for all term t, if (t sigma^n) converges to t', then sigma'(t) = t'
*)
let sat_subst (sigma:Term.subst) : Term.subst =
  List.fold_left
    (fun s e ->
       match e with
       | Term.ESubst (Var u, Var v) when u = v -> s (* useless mapping *)

       | ESubst (Var u, Var _) when
           Term.subst_var s u <> u -> (* u is one of the ui, already mapped *)
         s

       | ESubst (Var u, Var v) when (* u -> v is vi -> ui for some i: useless *)
           (List.exists
              (fun e -> match e with
                 | Term.ESubst (Var u', Var v') -> u = v' && v = u'
                 | _ -> assert false)
              s) ->
         s

       | ESubst (Var u, Var v) when (* u -> v is vj -> ui for some i <> j *)
           (List.exists
              (fun e -> match e with
                 | Term.ESubst (Var _, Var v') -> u = v'
                 | _ -> assert false)
              s) &&
           (Term.subst_var s v <> v) -> (* v already bound *)
         let w = Term.subst_var s v in (* w is vi, from ui -> vi *)
         (* replace any uj' -> vj' such that u = vj' with uj' -> vi *)
         let s' = List.map
             (fun e -> match e with
                | Term.ESubst (Var u', Var v') when u = v' ->
                  Term.ESubst (Term.mk_var u', Term.mk_var w)
                | _ -> e)
             s
         in
         (* add u -> vi *)
         (Term.ESubst (Term.mk_var u, Term.mk_var w)) :: s'

       | ESubst (Var u, Var v) when (* u -> v is vj -> v for some j,
                                       and v <> ui for all i *)
           (List.exists
              (fun e -> match e with
                 | Term.ESubst (Var _, Var v') -> u = v'
                 | _ -> assert false)
              s) ->
         (* replace any uj' -> vj' such that u = vj' with uj' -> v *)
         let s' = List.map
             (fun e -> match e with
                | Term.ESubst (Var u', Var v') when u = v' ->
                  Term.ESubst (Term.mk_var u', Term.mk_var v)
                | _ -> e)
             s
         in
         (* add u -> v *)
         (ESubst (Term.mk_var u, Term.mk_var v)) :: s'

       | ESubst (Var u, Var v) when (* u -> v is u -> ui for some i,
                                       and u <> vj for all j *)
           Term.subst_var s v <> v -> (* v already bound *)
         (* add u -> ui *)
         (ESubst (Term.mk_var u, Term.mk_var (Term.subst_var s v))) :: s

       | ESubst (Var u, Var v) -> (* u -> v with u <> vi, v <> ui for all i,j *)
         (* add u -> v *)
         (ESubst (Term.mk_var u, Term.mk_var v)) :: s

       | _ -> assert false)
    sigma []


(*------------------------------------------------------------------*)
(** Interprets phi as phi_1 /\ … /\ phi_n,
    keeps all phi_i of the form i = j where
    i is in fv (ie will be univ/ex quantified) and j is not (or conversely),
    as well as i = j when i and j are both in fv;
    and returns the substitution mapping such i's to the corresponding j
    (after saturation) *)
let find_equalities
  (fv : Vars.vars)
  (phi : Term.term)
  : Term.subst 
  =
  let phis = Term.decompose_ands phi in
  let sigma = (* first, equalities i = j with i free and not j or conversely *)
    List.filter_map (fun x -> x)
      (List.map
         (fun t ->
            match Term.destr_eq t with
            | Some (Var u, Var v) when List.mem u fv && not (List.mem v fv) ->
              Some (Term.ESubst (Term.mk_var u, Term.mk_var v))
            | Some (Var v, Var u) when List.mem u fv && not (List.mem v fv) ->
              Some (Term.ESubst (Term.mk_var u, Term.mk_var v))
            | _ -> None)
         phis)
  in

 let sigma' = (* then, equalities i = j with i and j free *)
    List.filter_map (fun x -> x)
      (List.map
         (fun t ->
            match Term.destr_eq t with
            | Some (Term.Var u, Var v) when List.mem u fv && List.mem v fv ->
              Some (Term.ESubst (Term.mk_var u, Term.mk_var v))
            | _ -> None)
         phis)
  in

  (* saturate sigma' (sigma already is) *)
  let sigma' = sat_subst sigma' in

  (* for any u -> v in sigma',
     - if v -> w in sigma replace u -> v with u -> w
     - if u -> w in sigma replace u -> v with v -> w *)
  (* this way, when we have u = v for free variables, if the other equalities
     imply that v = w we sigma o sigma' will first replace u with w
     and then v with w,
     and if they imply that u = w then it will replace v with w
     and then u with w
     (rather than only replacing u or v, and being left with u = w) *)
  let sigma' = List.map
      (fun e -> match e with
         | Term.ESubst (Var u, Var v) when Term.subst_var sigma v <> v ->
           Term.ESubst (Term.mk_var u, Term.mk_var (Term.subst_var sigma v))
         | ESubst (Var u, Var v) when Term.subst_var sigma u <> u ->
           Term.ESubst (Term.mk_var v, Term.mk_var (Term.subst_var sigma u))
         | _ -> e)
      sigma' in
  sigma' @ sigma


(*------------------------------------------------------------------*)
(** Interprets phi as phi_1 /\ … /\ phi_n,
    with each phi_i as phi'_1 \/ … \/ phi'_m
    and reconstructs it to simplify trivial equalities *)
(* not pretty, very ad hoc… *)
let clear_trivial_equalities (phi : Term.term) : Term.term =
  let phis = Term.decompose_ands phi in
  let phis =
    List.filter_map (fun x -> x)
      (List.map
         (fun phi' ->
            let phis' = Term.decompose_ors phi' in
            let phis' =
              List.filter_map (fun x -> x)
                (List.map
                   (fun t ->
                      match Term.destr_neq t with
                      | Some (u, v) when u = v -> None
                      | None when t = Term.mk_false -> None
                      | _ -> Some t)
                   phis')
            in
            let phi' = Term.mk_ors ~simpl:true phis' in
            match Term.destr_eq phi' with
            | Some (u, v) when u = v -> None
            | None when phi' = Term.mk_true -> None
            | _ -> Some phi')
         phis)
  in
  Term.mk_ands ~simpl:true phis

(** See `.mli` *)
let time_formula
    (a : Term.term) ?(path_cond : PathCond.t = PathCond.Top) (ts:ts_occs) : Term.term 
  =
  let phis =
    List.map (fun (ti:ts_occ) ->
      (* refresh probably not necessary, but doesn't hurt *)
      let tivs, s = Term.refresh_vars ti.so_vars in
      let ticnt   = Term.subst s ti.so_cnt in
      let ticond  = List.map (Term.subst s) ti.so_cond in

      Term.mk_exists ~simpl:true
        tivs
        (Term.mk_ands ~simpl:true ( PathCond.apply path_cond a ticnt :: ticond))
        (* in the simplest cases (when [path_cond = PathCond.Top]), 
             [PathCond.apply path_cond a ticnt] 
           is just
             [Term.mk_timestamp_leq a ticnt] 
        *)
    ) ts
  in
  Term.mk_ors ~simpl:true phis

(*------------------------------------------------------------------*)
(** {2 Proof obligations for a name occurrence} *)

(** Constructs the formula
      "exists free vars.
        (exists t1.occ_vars. action ≤ t1.occ_cnt ||
         … ||
         exists tn.occ_vars. action ≤ tn.occ_cnt) &&
        conditions of occ &&
        the occ is a collision"
    (this last part produced by [phiocc]) which will be the condition of the 
    proof obligation when finding the occurrence [occ].

    - [action] is the action producing the occurrence [occ] (for indirect 
      occurrences).
    - [ts = \[t1; …; tn\]] are the timestamp occurrences in [t].
    - The free vars of [occ.occ_cnt], [action], and [cond] not bound
      in the sequent's env should be in [occ.occ_vars],
      which is the case if [occ] was produced correctly
      (i.e. by [Match.fold] given either empty (for direct occurrences)
       or [iocc_vars] (for indirect occurrences)).
    - The free vars of [ts] should be all be bound in the sequent's env.

    If [negate] is set to [true], returns instead the negation of that formula. *)
let occurrence_formula
    ?(use_path_cond = false)
    ~(negate : bool)
    (phiocc  : ('a, 'b) occ_formula)
    (occ     : ('a, 'b) ext_occ)
  : Term.term
  =
  let o    = occ.eo_occ in
  let fv   = o.so_vars in
  let ts   = occ.eo_source_ts in
  let cond = o.so_cond in

  (* the formula "cnt is a collision" (or its negation) *)
  let phi_cnt = phiocc ~negate o.so_cnt o.so_coll o.so_ad in

  let phi_cond_cnt =
    if not negate then
      Term.mk_ands ~simpl:true (cond @ [phi_cnt])
    else
      Term.mk_impls ~simpl:true cond phi_cnt
  in 

  (* get in phi_cond_cnt the equalities forcing
     certain vars of the occ to be equal *)
  (* if negate, this will most likely do nothing, but that's fine *)
  let sigma : Term.subst = find_equalities fv phi_cond_cnt in

  (* we apply this substitution in the formula we generate.
     Produces logically equivalent, but simpler, formulas. *)
  let phi_cond_cnt = Term.subst sigma phi_cond_cnt in
  let phi_cond_cnt =
    (* remove trivial equalities, but not when generating the negation
       as it is confusing (or is it?) *)
    if not negate then clear_trivial_equalities phi_cond_cnt else phi_cond_cnt
  in

  match o.so_occtype with
  | EI_indirect a ->
    (* indirect occurrence: we also generate the timestamp inequalities *)
    let a = Term.subst sigma a in
    (* no need to substitute ts. *)
    (* all variables in ts are quantified existentially,
       so they cannot be the renamed variables. *)
    (* imprecise: they could initially have been the same as vars in the occ,
       but we forgot it.
       if we want to improve that, we'd need to only ex quantify the vars
       in ts not bound in the occ,
       but that's tricky, as it also means these vars can't be used
       to unify when subsuming timestamps *)
    let phi_time = 
      let path_cond = if use_path_cond then occ.eo_path_cond else PathCond.Top in
      time_formula ~path_cond a ts
    in

    if not negate then
      Term.mk_exists ~simpl:true fv (Term.mk_and  ~simpl:true phi_time phi_cond_cnt)
    else
      Term.mk_forall ~simpl:true fv (Term.mk_impl ~simpl:true phi_time phi_cond_cnt)

  | EI_direct -> (* direct occurrence *)
    if not negate then
      Term.mk_exists ~simpl:true fv phi_cond_cnt
    else
      Term.mk_forall ~simpl:true fv phi_cond_cnt


(** occurrence formula for names *)
let name_occurrence_formula ?use_path_cond = 
  (occurrence_formula ?use_path_cond) name_occ_formula

(*------------------------------------------------------------------*)
(** {1 Proof obligations for name occurrences} *)

(** Exported. *)
let occurrence_formulas_with_occs
    ~(mode : Iter.allowed_constants)   (* allowed sub-terms without further checks *)
    ?use_path_cond
    ?(negate      : bool = false)
    ?(pp_ns       : unit Fmt.t option = None)
    (phi_acc      : ('a, 'b) occ_formula)
    (get_bad_occs : ('a, 'b) f_fold_occs)
    (contx        : Constr.trace_cntxt)
    (env          : Env.t)
    (sources      : Term.terms)
  : Term.terms * Term.terms * name_occs * ('a, 'b) ext_occs
  =
  let conv = phi_acc in
 (* I leave the name [conv] to see when it's just used to compare *)

  (* compute occurrences [occs] and [accs] *)
  let occs, accs = 
    find_all_occurrences ~mode ~pp_ns conv get_bad_occs contx env sources 
  in

  (* translate [occs] as formulas *)
  let foccs = List.map (name_occurrence_formula ?use_path_cond ~negate) occs in

  (* translate [accs] as formulas *)
  let faccs = List.map (occurrence_formula ?use_path_cond ~negate phi_acc) accs in

  (foccs, faccs, occs, accs)

(*------------------------------------------------------------------*)
(** Exported. 
    Specialization of [occurrence_formulas_with_occs]. *)
let occurrence_formulas
    ~(mode : Iter.allowed_constants)   (* allowed sub-terms without further checks *)
    ?use_path_cond
    ?(negate      : bool=false)
    ?(pp_ns       : (unit Fmt.t) option=None)
    (phi_acc      : ('a, 'b) occ_formula)
    (get_bad_occs : ('a, 'b) f_fold_occs)
    (contx        : Constr.trace_cntxt)
    (env          : Env.t)
    (sources      : Term.terms)
  : Term.terms * Term.terms
  =
  let (occs, accs, _, _) =
    occurrence_formulas_with_occs
      ~mode ?use_path_cond ~negate ~pp_ns phi_acc
      get_bad_occs contx env sources
  in
  (occs, accs)

(*------------------------------------------------------------------*)
(** Exported. 
    Specialization of [occurrence_formulas_with_occs]. *)
let name_occurrence_formulas
    ~(mode : Iter.allowed_constants)   (* allowed sub-terms without further checks *)
    ?use_path_cond
    ?(negate      : bool=false)
    ?(pp_ns       : (unit Fmt.t) option=None)
    (get_bad_occs : (unit, unit) f_fold_occs)
    (contx        : Constr.trace_cntxt)
    (env          : Env.t)
    (sources      : Term.terms)
  : Term.terms 
  =
  let (occs, _) =
    occurrence_formulas
      ~mode ?use_path_cond ~negate ~pp_ns empty_occ_formula
      get_bad_occs contx env sources
  in
  occs
