(** See description of the module in the `.mli` *)

(*------------------------------------------------------------------*)
open Utils
open Ppenv

module MP = Match.Pos
module SE = SystemExpr

module Sv = Vars.Sv

module TraceHyps = Hyps.TraceHyps
module PathCond  = Iter.PathCond

(*------------------------------------------------------------------*)
(** Exported (see `.mli`) *)
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

(*------------------------------------------------------------------*)
(** Occurrence content *)

(** Exported (see `.mli`) *)
module type OccurrenceContent =
sig
  type content
  type data
  val collision_formula :
    negate:bool -> content:content -> collision:content ->
    data:data -> Term.term
  val subst_content : Term.subst -> content -> content
  val subst_data : Term.subst -> data -> data
  val pp_content : content formatter_p
  val pp_data : data formatter_p
end

type rec_content = {
  value : Term.term;
  order : Symbols.fname;
}

(*------------------------------------------------------------------*)
(** Exported (see `.mli`) *)
module RecArgContent : OccurrenceContent with type content = rec_content
                                      and type data = unit =
struct
  type content = rec_content
  type data = unit

  let collision_formula 
      ~(negate : bool) ~(content : content) ~(collision : content)
      ~(data : unit) 
    : Term.term 
    =
    ignore data;
    let content, collision = content.value, collision.value in
    if Type.equal (Term.ty content) (Term.ty collision) then
      if not negate then
        Term.mk_eq ~simpl:true content collision
      else
        Term.mk_not ~simpl:false (Term.mk_eq ~simpl:false content collision)
    else
      if negate then Term.mk_true else Term.mk_false

  let subst_content s c = {c with value = Term.subst s c.value}

  let subst_data _ () = ()

  let pp_content ppe fmt t = Fmt.pf fmt "(%a,%a)" (Term._pp ppe) t.value (Symbols.pp_path) t.order

  let pp_data _ppe (fmt : Format.formatter) () : unit =
    Fmt.pf fmt ""
end

(*------------------------------------------------------------------*)
(** Exported (see `.mli`) *)
module EmptyContent : OccurrenceContent with type content = unit
                                         and type data = unit =
struct
  type content = unit
  type data = unit
  let collision_formula 
      ~(negate : bool) ~(content:unit) ~(collision:unit)
      ~(data : unit) : Term.term =
    ignore content;
    ignore collision;
    ignore data;
    if not negate then Term.mk_true
    else Term.mk_false

  let subst_content _ () = ()

  let subst_data _ () = ()

  let pp_content _ppe (fmt:Format.formatter) () = Fmt.pf fmt ""

  let pp_data = pp_content
end

(*------------------------------------------------------------------*)
(** Simple occurrences *)

(** Exported (see `.mli`) *)
type occ_type =
  | EI_direct
  | EI_indirect of Term.term * Symbols.macro


(** Exported (see `.mli`) *)
let subst_occtype (sigma : Term.subst) (ot : occ_type) : occ_type =
  match ot with
  | EI_direct -> EI_direct
  | EI_indirect (a,f) -> EI_indirect (Term.subst sigma a,f)

(** Exported (see `.mli`) *)
type occ_show = Show | Hide | ShowContentOnly


(*------------------------------------------------------------------*)
(** Exported (see `.mli`) *)
module type SimpleOcc = sig
  module OC : OccurrenceContent
  type content = OC.content
  type data = OC.data
  type simple_occ =
    {so_cnt     : content;
     so_coll    : content;
     so_ad      : data;
     so_vars    : Vars.vars;
     so_cond    : Term.terms;
     so_occtype : occ_type;
     so_subterm : Term.term;
     so_show    : occ_show;
    }

  type simple_occs = simple_occ list

  val mk_simple_occ :
    content:content -> collision:content -> data:data ->
    vars:Vars.vars -> cond:Term.terms -> typ:occ_type ->
    sub:Term.term -> show:occ_show -> simple_occ

  val aux_occ_incl :
    Symbols.table -> SE.fset -> ?mv:Match.Mvar.t ->
    simple_occ -> simple_occ -> Match.Mvar.t option

  val occ_incl :
    Symbols.table -> SE.fset -> simple_occ -> simple_occ -> bool

  val clear_subsumed :
    Symbols.table -> SE.fset -> simple_occs -> simple_occs

  val pp : simple_occ formatter_p
end

(*------------------------------------------------------------------*)
(** Exported (see `.mli`) *)
module MakeSO (OC:OccurrenceContent) : (SimpleOcc with module OC = OC) =
struct
  module OC = OC

  type content = OC.content

  type data = OC.data

  (** Exported (see `.mli`) *)
  type simple_occ =
    {so_cnt     : content;
     so_coll    : content;
     so_ad      : data;
     so_vars    : Vars.vars;
     so_cond    : Term.terms;
     so_occtype : occ_type;
     so_subterm : Term.term;
     so_show    : occ_show;
    }

  type simple_occs = simple_occ list

  (** Exported (see `.mli`) *)
  let mk_simple_occ
      ~(content : content) ~(collision : content) ~(data : data)
      ~(vars : Vars.vars) ~(cond : Term.terms) ~(typ : occ_type)
      ~(sub : Term.term) ~(show:occ_show)
    : simple_occ 
    =
    let vars, sigma = Term.refresh_vars vars in
    {so_cnt  = OC.subst_content sigma content;
     so_coll = OC.subst_content sigma collision;
     (* variables bound above the occurrence can actually occur in coll.
        That happens eg for ind-cca, where we construct
        collisions between two encryption randomnesses
        that may be under binders. *)
     so_ad   = OC.subst_data sigma data; 
     so_vars = vars;
     so_cond = List.map (Term.subst sigma) cond;
     so_occtype = subst_occtype sigma typ;
     so_subterm = sub; (* don't rename in sub, to keep it more readable *)
     so_show = show;
    }


  (** Internal.
      Checks if [t1] is included in the patterm [pat2], i.e. [t1 ∈ occ2].
      Starting from a matching function mv, returns the new mv *)
  let pat_subsumes
      (table : Symbols.table)
      (system : SE.fset)
      ?(mv : Match.Mvar.t = Match.Mvar.empty)
      (t1 : Term.term) (pat2 : Term.term Term.pat_op)
    : Match.Mvar.t option
    =
    assert (pat2.pat_op_params = Params.Open.empty);
    let context = SE.reachability_context system in
    match Match.T.try_match ~param:Match.crypto_param ~mv table context t1 pat2
    with
    | NoMatch _ -> None
    | Match mv -> Some mv
  (* no type substitution since [pat_tyvars = \[\]]. *)


  (** Exported (see `.mli`) *)
  let aux_occ_incl
      (table : Symbols.table)
      (system : SE.fset)
      ?(mv : Match.Mvar.t = Match.Mvar.empty)
      (o1 : simple_occ)
      (o2 : simple_occ)
    : Match.Mvar.t option =
    (* we ignore the subterm: it will be different, but doesn't matter *)
    (* we don't care about the variables bound above being the same,
       as we rename *)

    (* we check that the print flags are the same *)
    if o1.so_show <> o2.so_show then None
    else
      begin
        (* build a dummy term, which we use to match in one go many elements
           of the two occurrences *)
        (* TODO: there's no real reason to use boolean formulas,
           rather than just terms *)
        let mk_dummy (o : simple_occ) : Term.term =
          let phi_f =
            OC.collision_formula ~negate:false ~content:o.so_cnt
              ~collision:o.so_coll ~data:o.so_ad in
          let phi_ac = match o.so_occtype with
            | EI_direct -> Term.mk_eq ~simpl:false Term.mk_false Term.mk_false
            | EI_indirect (a,_) -> Term.mk_eq ~simpl:false a a
          in
          Term.mk_ands ~simpl:false [phi_f; phi_ac]
        in
        let pat2 = Term.{
            pat_op_params = Params.Open.empty;
            pat_op_vars   = Vars.Tag.local_vars o2.so_vars;
            (* local information, since we allow to match diff operators *)

            pat_op_term   = mk_dummy o2;
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

          let mk_cond2 cond2 = { pat2 with pat_op_term = cond2; } in
          let b = (* construct the inst. of cond2 on the fly,
                     so maybe we get the wrong one and
                     conclude it's not included.
                     still fine, that's an overapproximation *)
            List.for_all (fun cond2 ->
                List.exists (fun cond1 ->
                    match
                      pat_subsumes ~mv:(!mv) table system
                        cond1 (mk_cond2 cond2)
                    with
                    | None -> false
                    | Some mv' -> mv := mv'; true
                  ) o1.so_cond
              ) o2.so_cond
          in
          if b then Some !mv else None
      end

  (** Exported (see `.mli`) *)
  let occ_incl
      (table : Symbols.table)
      (system : SE.fset)
      (o1 : simple_occ)
      (o2 : simple_occ)
    : bool =
    match aux_occ_incl table system o1 o2 with
    | Some _ -> true
    | None -> false


  (** Exported (see `.mli`) *)
  let clear_subsumed
      (table : Symbols.table)
      (system : SE.fset)
      (occs : simple_occs) :
    simple_occs =
    List.clear_subsumed (occ_incl table system) occs


  (** Internal.
      Prints a description of the occurrence. *)
  let pp_internal ppe (ppf:Format.formatter) (o:simple_occ) : unit =
    (* we don't print the data. maybe we would like to sometimes?*)
    match o.so_show, o.so_occtype with
    | Hide, _ -> ()
    | Show, EI_indirect (a,_) ->
      Fmt.pf ppf
        "@[%a@] @,(collision with @[%a@])@ in action \
         @[%a@]@ @[<hov 2>in term@ @[%a@]@]"
        (OC.pp_content ppe) o.so_cnt
        (OC.pp_content ppe) o.so_coll
        (Term._pp      ppe) a
        (Term._pp      ppe) o.so_subterm
    | ShowContentOnly, EI_indirect (a,_) ->
      Fmt.pf ppf
        "@[%a@] @,in action @[%a@]@ @[<hov 2>in term@ @[%a@]@]"
        (OC.pp_content ppe) o.so_cnt
        (Term._pp      ppe) a
        (Term._pp      ppe) o.so_subterm
    | Show, EI_direct ->
      Fmt.pf ppf
        "@[%a@] @,(collision with @[%a@])@ @[<hov 2>in term@ @[%a@]@]"
        (OC.pp_content ppe) o.so_cnt
        (OC.pp_content ppe) o.so_coll
        (Term._pp      ppe) o.so_subterm
    | ShowContentOnly, EI_direct ->
      Fmt.pf ppf
        "@[%a@] @,@[<hov 2>in term@ @[%a@]@]"
        (OC.pp_content ppe) o.so_cnt
        (Term._pp      ppe) o.so_subterm

  (** Exported (see `.mli`) *)
  let pp ppe (fmt:Format.formatter) (o:simple_occ) : unit =
    Fmt.pf fmt "@[<hv 2>%a@]" (pp_internal ppe) o

end

(*------------------------------------------------------------------*)
(** Exported (see `.mli`) *)
module RecArgOcc : (SimpleOcc with module OC = RecArgContent) =
struct
  include MakeSO(RecArgContent)

  (** Overwrite the standard aux function to handle pred more precisely *)
  let aux_occ_incl
      (table : Symbols.table)
      (system : SE.fset)
      ?(mv : Match.Mvar.t = Match.Mvar.empty)
      (ts1 : simple_occ)
      (ts2 : simple_occ)
    : Match.Mvar.t option =
    let f = aux_occ_incl table system in
    match f ~mv ts1 ts2 with
    | Some mv -> Some mv
    | None ->
      if Type.equal (Term.ty ts1.so_cnt.value) Type.ttimestamp
      && Type.equal (Term.ty ts2.so_cnt.value) Type.ttimestamp
      && Symbols.path_equal ts1.so_cnt.order Library.Prelude.fs_lt
      && Symbols.path_equal ts2.so_cnt.order Library.Prelude.fs_lt                                
      then
        f ~mv ts1 {ts2 with so_cnt = {ts2.so_cnt with value = Term.mk_pred ts2.so_cnt.value}}
      else None
  (* if ts1 not incl in ts2, also try ts1 incl in pred(ts2) *)
  (* as "t <= pred(ts2) \/ t <= ts2" is the same as "t <= ts2" *)
  (* Note that this works because we only use ts_occs to generate
     formulas of this form (disjunction of inequalities) *)


  (** Overwrite the standard occ_incl to use the precise aux function *)
  let occ_incl
      (table : Symbols.table)
      (system : SE.fset)
      (ts1 : simple_occ)
      (ts2 : simple_occ)
    : bool =
    match aux_occ_incl table system ts1 ts2 with
    | Some _ -> true
    | None -> false


  (** Overwrite the standard clear_subsumed to use the precise occ_incl *)
  let clear_subsumed
      (table : Symbols.table)
      (system : SE.fset)
      (occs : simple_occs) :
    simple_occs =
    List.clear_subsumed (occ_incl table system) occs
end 

type rec_arg_occ = RecArgOcc.simple_occ
type rec_arg_occs = RecArgOcc.simple_occs


(** Exported (see `.mli`) *)
module EmptyOcc : (SimpleOcc with module OC = EmptyContent) =
  MakeSO (EmptyContent)
type empty_occ = EmptyOcc.simple_occ
type empty_occs = EmptyOcc.simple_occs


(*------------------------------------------------------------------*)
(** Extended occurrences *)

(** Exported (see `.mli`) *)
module type ExtOcc = sig
  module SO:SimpleOcc
  type simple_occ = SO.simple_occ

  type ext_occ = {
    eo_occ            : simple_occ;
    eo_source         : Term.terms;
    eo_source_rec_arg : rec_arg_occs;
    eo_path_cond      : Iter.PathCond.t;
  }

  type ext_occs = ext_occ list

  val ext_occ_incl :
    Symbols.table -> SE.fset -> ext_occ -> ext_occ -> bool

  val clear_subsumed :
    Symbols.table -> SE.fset -> ext_occs -> ext_occs

  val pp : ext_occ formatter_p

  val pp_occs : ext_occs formatter_p
end


(*------------------------------------------------------------------*)
(** Exported (see `.mli`) *)
module MakeEO (SO:SimpleOcc) : (ExtOcc with module SO = SO) =
struct
  module SO = SO

  type simple_occ = SO.simple_occ

  (** Exported (see `.mli`) *)
  type ext_occ = {
    eo_occ            : simple_occ;
    eo_source         : Term.terms;
    eo_source_rec_arg : rec_arg_occs;     
    eo_path_cond      : Iter.PathCond.t;
  }

  type ext_occs = ext_occ list

  (** Exported (see `.mli`) *)
  let ext_occ_incl
      (table : Symbols.table)
      (system : SE.fset)
      (occ1 : ext_occ)
      (occ2 : ext_occ)
    : bool =
    let mv = SO.aux_occ_incl table system occ1.eo_occ occ2.eo_occ in
    match mv with
    | None -> false
    | Some mv ->
      (* still have to check [eo_path_cond], [occ_type] and [source_ts] *)
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
                RecArgOcc.aux_occ_incl ~mv:(!mv) table system ts1 ts2
              with
              | None -> false
              | Some mv' -> mv := mv'; true
            ) occ2.eo_source_rec_arg
        ) occ1.eo_source_rec_arg


  (** Exported (see `.mli`) *)
  let clear_subsumed
      (table : Symbols.table)
      (system : SE.fset)
      (occs : ext_occs)
    : ext_occs =
    List.clear_subsumed (ext_occ_incl table system) occs

  (** Exported (see `.mli`) *)
  let pp ppe (fmt:Format.formatter) (occ:ext_occ) : unit =
    (SO.pp ppe) fmt occ.eo_occ

  (** Exported (see `.mli`) *)
  let pp_occs ppe (fmt:Format.formatter) (occs:ext_occs) : unit =
    let occs = List.filter (fun o -> o.eo_occ.so_show <> Hide) occs in
    if occs = [] then
      Fmt.pf fmt "(no occurrences)@;"
    else
      Fmt.list ~sep:(Fmt.any "@;@;") (pp ppe) fmt occs
end


(*------------------------------------------------------------------*)
(** Macro expansion *)

(** Exported (see `.mli`) *)
type pos_info =
  { pi_pos     : MP.pos;
    pi_occtype : occ_type;
    pi_context : ProofContext.t;
    pi_vars    : Vars.vars;
    pi_cond    : Term.terms;
    pi_subterm : Term.term;
  }

(** Exported (see `.mli`) *)
type expand_info = occ_type * ProofContext.t

(** Exported (see `.mli`) *)
let get_expand_info (pi : pos_info) : expand_info =
  (pi.pi_occtype, pi.pi_context)


(** Exported (see `.mli`) *)
let expand_macro_check_once
    ((ot, c):expand_info) (t : Term.term) : Term.term option
  =
  match t with
  | Macro (m, l, ts) ->
    begin
      match ot with
      | EI_direct ->
        let res, has_red =
          Match.reduce_delta_macro1
            ~constr:true c.env ~hyps:c.hyps t
        in
        if has_red = True then Some res else None
      | EI_indirect _ ->
        begin
          (* In the indirect case, we always expand, so we ignore the potential cond *)
          match Macros.unfold c.env m l ts with
          | `Results [r] ->            
            Some (Term.mk_ite
                    r.when_cond
                    r.out
                    (Library.Prelude.mk_witness c.env.table ~ty_arg:(Term.ty r.out)))
          | _ -> None
        end
    end
  | _ -> None

(** Exported (see `.mli`) *)
let rec expand_macro_check_all (info:expand_info) (t:Term.term) : Term.term =
  match expand_macro_check_once info t with
  | Some t' -> expand_macro_check_all info t'
  | None -> t

(*------------------------------------------------------------------*)
(** Check that if [t]'s top-level construct is a quantifier, then it
    is over enumarable types. *)
let check_top_quantifier_enumerable table (t : Term.t) : unit =
  match t with
  (* no checks for [Lambda] *)
  | Find (es, _, _, _)
  | Quant ((Seq | ForAll | Exists), es, _) -> 
    let not_enum =
      List.map Vars.ty es |>
      List.filter (not -| Symbols.TyInfo.is_enum table)
    in
    if not_enum <> [] then
      Tactics.soft_failure
        (Failure
           (Fmt.str "@[<hov 2>quantifier%s over non-enumerable type:@ @[%a@]@]"
              (if List.length not_enum > 1 then "s" else "")
              (Fmt.list ~sep:Fmt.comma Type.pp) not_enum) );

  | _ -> ()

(*------------------------------------------------------------------*)
let get_rec_args_ext
    ~(mode : Iter.allowed ) (* allowed sub-terms without further checks *)
    (t : Term.term)
    (info : expand_info)
  : rec_arg_occs
  =
  let occ_type, context = info in
  (* sanity check: this function is meant to be called on the initial
     direct terms (the sources from which other occs come),
     not inside indirect occs *)
  assert (occ_type = EI_direct);

  let env    = context.env in
  let table  = env.table in
  let system = env.system in

  let rec get 
      (t : Term.term)
      ~(fv:Vars.vars) ~(cond:Term.terms) ~(p:MP.pos) ~(se:SE.arbitrary)
    : rec_arg_occs
    =
    let system = { system with set = se; } in
    let context = Iter.update_context ~extra_vars:fv system context in
    let env = context.env in
    assert (Sv.subset (Term.fv t) (Vars.to_vars_set env.vars));

    (* Put [t] in weak head normal form w.r.t. rules in
       [Reduction.rp_crypto].  

       Must be synchronized with corresponding code in [fold_bad_occs]
       and [Occurrences.fold_bad_occs]. *)
    let t =
      let red_param = Reduction.rp_crypto in
      let st = Reduction.mk_state context ~red_param in
      let strat = Reduction.(MayRedSub rp_full) in
      fst (Reduction.whnf_term ~strat st t)
    in

    match t with
    | _ when mode = PTimeSI  
          && HighTerm.is_ptime_deducible ~si:true  env t -> []
    | _ when mode = PTimeNoSI 
          && HighTerm.is_ptime_deducible ~si:false env t -> []
    | _ when mode = NoHonestRand &&
             (HighTerm.is_constant env t ||
              HighTerm.is_ptime_deducible ~si:false env t) -> []

    | Term.Var v -> 
      let err_str =
        Fmt.str "terms contain a %s: @[%a@]"
          (match mode with
           | NoHonestRand -> "variable that may depend on honest randomness" 
           | PTimeSI | PTimeNoSI -> "non-ptime variable")
          Vars.pp v
      in
      Tactics.soft_failure (Tactics.Failure err_str)

    | Macro (m, l, ts) ->
      begin
        let info =
          ( occ_type,
            ProofContext.change_system ~system:{ system with set = se; } context)
        in
        match expand_macro_check_once info t with
        | Some t' -> get ~fv ~cond ~p ~se t'
        | None ->
          let ts =
            (* we force the unfolding of the following macros, 
               for a more precise rule *)
            if m.s_symb = Symbols.Classic.inp   || 
               m.s_symb = Symbols.Quantum.inp   || 
               m.s_symb = Symbols.Quantum.state 
            then {value = Term.mk_pred ts; order = Library.Prelude.fs_lt}
            else
              let value, order =
                Macros.get_macro_deacreasing_info table m.s_symb ts
              in
              {value; order}
          in
          let occ =
            RecArgOcc.mk_simple_occ
              ~content:ts
              ~collision:
                {value =Library.Prelude.mk_witness table ~ty_arg:Type.ttimestamp;
                 order= Library.Prelude.fs_lt
                }
              (* unused, so always set to some arbitrary value *)
              ~data:() (* unused *)
              ~vars:(List.rev fv) (* rev nicer for printing *)
              ~cond:cond
              ~typ:occ_type
              ~sub:Term.mk_false (* unused *)
              ~show:Hide
          in
          [occ] @ 
          List.concat_map (fun t ->
              get ~fv ~cond ~p ~se t
            ) (ts.value :: l)
      end

    | _ ->
      check_top_quantifier_enumerable table t;

      MP.fold_shallow
        (fun t' se fv cond p occs ->
           occs @ (get t' ~fv ~cond ~p ~se))
        ~se ~fv ~p ~cond [] t
  in
  get t ~fv:[] ~cond:[] ~p:MP.root ~se:system.set


(** Returns all recursive arguments occuring in macros in a list of terms.
    Should only be used when sources are directly occurring,
    not themselves produced by unfolding macros. *)
let get_macro_rec_args
    ~(mode    : Iter.allowed)   (* allowed sub-terms without further checks *)
    ~(context : ProofContext.t)
    (sources  : Term.terms) : rec_arg_occs
  =
  let ei = (EI_direct, context) in
  let env = context.env in
  let actions =
    List.concat_map (fun t -> get_rec_args_ext ~mode t ei) sources
  in
  RecArgOcc.clear_subsumed env.table (SE.to_fset env.system.set) actions

(*------------------------------------------------------------------*)
(** Occurrence search *)

(** Exported (see `.mli`) *)
module type OccurrenceSearch = sig

  module EO : ExtOcc
  type simple_occ = EO.simple_occ
  type simple_occs = simple_occ list
  type ext_occ = EO.ext_occ
  type ext_occs = ext_occ list

  type f_fold_occs =
    retry:(unit -> simple_occs) ->
    rec_call:(pos_info -> Term.term -> simple_occs) ->
    pos_info ->
    Term.term ->
    simple_occs

  val find_all_occurrences :
    mode:Iter.allowed ->
    ?pp_descr:unit Fmt.t option ->
    f_fold_occs ->
    ProofContext.t ->
    Term.terms ->
    ext_occs
end


(** Exported (see `.mli`) *)
module MakeSearch (OC:OccurrenceContent) :
  (OccurrenceSearch with module EO.SO.OC = OC) =
struct

  module SO = MakeSO(OC)
  module EO = MakeEO(SO)

  type simple_occ = EO.simple_occ
  type simple_occs = simple_occ list
  type ext_occ = EO.ext_occ
  type ext_occs = ext_occ list

  (*------------------------------------------------------------------*)
  (** Exported (see `.mli`) *)
  type f_fold_occs =
    retry:(unit -> simple_occs) ->
    rec_call:(pos_info -> Term.term -> simple_occs) ->
    pos_info ->
    Term.term ->
    simple_occs

  (*------------------------------------------------------------------*)
  (** Internal.
      Given a [f_fold_occs] function [get_bad_occs],
      calls [get_bad_occs], is called again when [get_bad_occs] asks
      for recursive calls on subterms, and handles the case where
      get_bad_occs calls its first continuation (ie gives up) by 
      - 1) unfolding the term, if it's a macro that can be unfolded
      - 2) doing nothing, if it's a macro that can't be unfolded
        (in that case, [fold_macro_support] will generate a separate 
        [iocc] for that)
      - 3) using [Match.Pos.fold_shallow], to recurse on subterms
        at depth 1. *)
  let fold_bad_occs
      (get_bad_occs     : f_fold_occs)         (* bad occurrence function *)
      ~(fv              : Vars.vars)           (* initial free variables *)
      ((occtype, context) : expand_info)       (* initial proof-context *)
      (t                : Term.term)           (* initial term *)
    : simple_occs
    =
    (* instantiation of [get_bad_occs] on its continuation *)
    let rec get (pi : pos_info) (t : Term.term) : simple_occs =
      let context = pi.pi_context in

      (* Put [t] in weak head normal form w.r.t. rules in
         [Reduction.rp_crypto].

         Must be synchronized with corresponding code in
         [get_actions_ext], [Iter.fold_macro_support] and [Crypto]. *)
      let t =
        let red_param = Reduction.rp_crypto in
        let context =
          Iter.update_context
            ~extra_vars:pi.pi_vars
            context.env.system  (* use the same system, as we only add more vars *)
            context
        in
        let st = Reduction.mk_state context ~red_param in
        let strat = Reduction.(MayRedSub rp_full) in
        fst (Reduction.whnf_term ~strat st t)
      in

      (* recursing continuation of [get_bad_occs] for cases it does
         not handle *)
      let retry_on_subterms () : simple_occs =
        match t with
        | Macro _ -> (* expand if possible *)
          begin
            match expand_macro_check_once (occtype, context) t with
            | Some t' -> get pi t'
            | None -> []
            (* if we can't expand, do nothing.
               [fold_macro_support] will create another iocc
               for that macro, and it will be checked separately *)
          end

        | _ ->
          MP.fold_shallow
            (fun t' se fv cond p acc ->
               let context =
                 ProofContext.change_system
                   ~system:{ context.env.system with set = se; }
                   context
               in
               let new_st = if Term.is_binder t then t' else pi.pi_subterm in
               let pi =
                 {pi_pos=p; pi_occtype=pi.pi_occtype; pi_context=context;
                  pi_vars=fv; pi_cond=cond; pi_subterm = new_st}
               in
               let newacc = get pi t' in
               acc @ newacc)
            ~se:context.env.system.set ~fv:pi.pi_vars ~p:pi.pi_pos ~cond:pi.pi_cond [] t
      in

      get_bad_occs ~retry:retry_on_subterms ~rec_call:get pi t
    in

    (* initial position information *)
    let pi0 =
      {pi_pos=MP.root; pi_occtype=occtype; pi_context=context;
       pi_vars=fv; pi_cond=[]; pi_subterm=t}
    in
    get pi0 t

  (*------------------------------------------------------------------*)
  (** Exported.
      Given a function [find_occs] that generates a list of occurrences
      found in a term (obtained from [get_bad_occs]),
      expanding macros when possible according to [expand_info] but
      not otherwise (undef and maybedef macros will be handled by
      [fold_macro_support]);
      computes the list of all occurrences in the list of source terms.
      Relies on [fold_macro_support] to look through
      all macros in the term. *)
  let find_all_occurrences
      ~(mode        : Iter.allowed)   (* allowed sub-terms without further checks *)
      ?(pp_descr    : unit Fmt.t option = None)
      (get_bad_occs : f_fold_occs)
      (context      : ProofContext.t)
      (sources      : Term.terms) 
    : ext_occs
    =
    let env = context.env in
    let system = SE.to_fset env.system.set in
    let table = env.table in
    let ppe = default_ppe ~table () in

    let find_occs = fold_bad_occs get_bad_occs in

    (* printer for the thing we're looking for *)
    let ppp ppf = match pp_descr with
      | Some x -> Fmt.pf ppf "@[%a@] " x ()
      | None   -> Fmt.pf ppf ""
    in

    (* auxiliary function to keep only non-hidden occs (for printing) *)
    let filter_show occs =
      List.filter (fun o -> o.EO.eo_occ.so_show <> Hide) occs
    in

    if pp_descr <> None then Printer.pr "@[<v 0>";
    (* direct occurrences *)
    let dir_occs =
      List.fold_left
        (fun dir_occs t -> (* find direct occurrences in t *)
           (* recursive arguments occurring in t *)
           let rec_arg  = get_macro_rec_args ~mode ~context [t] in
           (* name occurrences in t *)
           let occs = find_occs ~fv:[] (EI_direct, context) t in
           (* add the info to the occurrences *)
           let occs = 
             List.map
               (fun o -> EO.{eo_occ=o; eo_source=[t]; eo_source_rec_arg=rec_arg;
                             eo_path_cond = Iter.PathCond.Top; }) 
               occs
           in

           (* printing *)
           let showoccs = filter_show occs in
           if pp_descr <> None && showoccs <> [] then
             Printer.pr "@[<hv 2>\
                         @[<hov 0>Direct @[%t@]@ in@ @[%a@]:@]\
                         @;@[%a@]@]@;@;@;"
               ppp Term.pp t (EO.pp_occs ppe) showoccs;
           dir_occs @ occs)
        []
        sources
    in

    (* indirect occurrences *)
    let ind_occs =
      Iter.fold_macro_support ~mode (fun iocc ind_occs ->
          (* todo: if fold_macro_support stored in iocc the fset
             for the place where the iocc was found, we could give it
             instead of [context] to find_occs *)
          (* todo: we could print which source the indirect occs came from,
             not sure that's useful though *)
          (* FIXME: quantum: we build the tuple [(iocc_cond, iocc_cnt)],
             while we used to only consider [iocc_cnt] (the condition
             [iocc_cond] is new). This makes the printing slightly less
             useful. How can this be fixed? (check this with Joseph). *)
          let t = Term.mk_tuple [iocc.iocc_cond; iocc.iocc_cnt] in
          (* For legacy reasons, we can't build t as what we ideally want, i.e: 
          let t = Term.mk_ite iocc.iocc_cond iocc.iocc_cnt
              (Library.Prelude.mk_witness table ~ty_arg:(Term.ty iocc.iocc_cnt)) in
          *)
          
          let sfv = iocc.iocc_vars in
          let src = iocc.iocc_sources in
          let a = iocc.iocc_rec_arg in

          (* a's free variables should always be in fv \cup env *)
          assert (Vars.Sv.subset
                    (Term.fv a)
                    (Vars.Sv.union sfv (Vars.to_vars_set env.vars)));
          (* recursive arguments occurring in sources (not in the indirect occs!) *)
          let rec_arg = get_macro_rec_args ~mode ~context src in
          (* indirect occurrences in iocc *)
          let occs =
            find_occs
              ~fv:(Vars.Sv.elements sfv) 
              (EI_indirect (a, iocc.iocc_fun), context) t
          in
          (* add the info *)
          let occs = 
            List.map
              (fun o -> 
                 EO.{ eo_occ            = o; 
                      eo_source         = src;
                      eo_source_rec_arg = rec_arg; 
                      eo_path_cond      = iocc.iocc_path_cond; }
              )
              occs
          in
          ind_occs @ occs)
        context sources []
    in

    (* printing *)
    let showoccs = filter_show ind_occs in
    if pp_descr <> None && showoccs <> [] then
      Printer.pr "@[<hv 2>@[Indirect @[%t@]@ in other actions:@]@;%a@]@;@;"
        ppp
        (EO.pp_occs ppe) showoccs;

    (* remove subsumed occs *)
    let occs = dir_occs @ ind_occs in
    let loccs = List.length (filter_show occs) in

    (* todo: this would need to change if the system depends on the occ *)
    let occs = EO.clear_subsumed table system occs in
    let loccs' = List.length (filter_show occs) in
    let lsub = loccs - loccs' in

    if pp_descr <> None && loccs <> 0 then
      (Printer.pr
         "Total: @[<v 0>%d occurrence%s@;"
         loccs (if loccs = 1 then "" else "s");
       Printer.pr
         "%d of them %s subsumed by another@;"
         lsub (if lsub = 1 then "is" else "are");
       Printer.pr
         "%d occurrence%s remaining@;@]"
         loccs' (if loccs' = 1 then "" else "s"));
    if pp_descr <> None then
      Printer.pr "@;@]";
    occs
end



(*------------------------------------------------------------------*)
(** Formula construction and simplification *)

(*------------------------------------------------------------------*)
(** Exported (see `.mli`) *)
let rec_arg_formula
    (table : Symbols.table)
    (a : Term.term) (caller : Symbols.macro) ?(path_cond : PathCond.t = PathCond.Top) (rec_args:rec_arg_occs)
  : Term.term =
  let a, ord = Macros.get_macro_deacreasing_info table caller a in
  let phis =
    List.map (fun (ti:rec_arg_occ) ->
        (* refresh probably not necessary, but doesn't hurt *)
        let tivs, s = Term.refresh_vars ti.so_vars in
        let ticnt   = RecArgContent.subst_content s ti.so_cnt in
        let ticond  = List.map (Term.subst s) ti.so_cond in
        let pcond =
          if Type.equal (Term.ty a) (Term.ty ticnt.value)
          && Symbols.path_equal ord ticnt.order 
          then
            PathCond.apply table path_cond a ticnt.value ticnt.order
            (* in the simplest cases (when [path_cond = PathCond.Top]),
               and we are over timestamps,
             [PathCond.apply path_cond a ticnt] 
             is just
             [Term.mk_timestamp_leq a ticnt] 
          *)
          else
            Term.mk_true
        in
        Term.mk_exists ~simpl:true
          tivs
          (Term.mk_ands ~simpl:true
             (pcond :: ticond))

      ) rec_args
  in
  Term.mk_ors ~simpl:true phis

(*------------------------------------------------------------------*)
(** Exported (see `.mli`) *)
module type OccurrenceFormulas = sig
  type ext_occ
  type ext_occs = ext_occ list

  val occurrence_formula :
    Symbols.table -> ?use_path_cond:bool -> negate:bool -> ext_occ -> Term.term
end

(** Exported (see `.mli`) *)
module MakeFormulas (EO:ExtOcc) :
  (OccurrenceFormulas with type ext_occ = EO.ext_occ) =
struct
  module OC = EO.SO.OC
  type ext_occ = EO.ext_occ
  type ext_occs = ext_occ list

  (*------------------------------------------------------------------*)
  (** Utilities to build the proof-obligations *)

  (*------------------------------------------------------------------*)
  (** Internal.
      Saturates a substitution sigma that maps variables to variables
      ie returns sigma' = [u1 -> v1, …, un -> vn] such that
      - forall i <> i'. ui <> ui'
      - forall i, j. ui <> vj
      - for all term t, t sigma is equal to t modulo the equalities ui = vi
      - for all term t, if (t sigma^n) converges to t', then sigma'(t) = t' *)
  let sat_subst (sigma:Term.subst) : Term.subst =
    List.fold_left
      (fun s e ->
         match e with
         | Term.ESubst (Var u, Var v) when u = v -> s (* useless mapping *)

         | ESubst (Var u, Var _) when
             Term.subst_var s u <> u -> (* u is one of the ui,
                                           already mapped *)
           s

         | ESubst (Var u, Var v) when (* u -> v is vi -> ui for some i:
                                         useless *)
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

         | ESubst (Var u, Var v) -> (* u -> v with u <> vi, v <> ui
                                       for all i,j *)
           (* add u -> v *)
           (ESubst (Term.mk_var u, Term.mk_var v)) :: s

         | _ -> assert false)
      sigma []

  (*------------------------------------------------------------------*)
  (** Internal.
      Interprets phi as phi_1 /\ … /\ phi_n,
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
    let sigma = (* first, equalities i = j with i free and not j
                   or conversely *)
      List.filter_map (fun x -> x)
        (List.map
           (fun t ->
              match Term.destr_eq t with
              | Some (Var u, Var v) when
                  List.mem u fv && not (List.mem v fv) ->
                Some (Term.ESubst (Term.mk_var u, Term.mk_var v))
              | Some (Var v, Var u) when
                  List.mem u fv && not (List.mem v fv) ->
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
    (* this way, when we have u = v for free variables,
       if the other equalities
       imply that v = w we sigma o sigma' will first replace u with w
       and then v with w,
       and if they imply that u = w then it will replace v with w
       and then u with w
       (rather than only replacing u or v, and being left with u = w) *)
    let sigma' = List.map
        (fun e -> match e with
           | Term.ESubst (Var u, Var v) when
               Term.subst_var sigma v <> v ->
             Term.ESubst (Term.mk_var u,
                          Term.mk_var
                            (Term.subst_var sigma v))
           | ESubst (Var u, Var v) when
               Term.subst_var sigma u <> u ->
             Term.ESubst (Term.mk_var v,
                          Term.mk_var
                            (Term.subst_var sigma u))
           | _ -> e)
        sigma' in
    sigma' @ sigma

  (*------------------------------------------------------------------*)
  (** Exported (see `.mli`) *)
  let occurrence_formula
      (table : Symbols.table)
      ?(use_path_cond = false)
      ~(negate : bool)
      (occ     : ext_occ)
    : Term.term
    =
    let o    = occ.eo_occ in
    let fv   = o.so_vars in
    let ts   = occ.eo_source_rec_arg in
    let cond = o.so_cond in
    (* the formula "cnt is a collision" (or its negation) *)
    let phi_cnt =
      OC.collision_formula ~negate
        ~content:o.so_cnt ~collision:o.so_coll ~data:o.so_ad
    in

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
      if not negate then clear_trivial_equalities phi_cond_cnt
      else phi_cond_cnt
    in

    match o.so_occtype with
    | EI_indirect (a,f) ->
      (* indirect occurrence: we also generate the timestamp inequalities *)
      let a = Term.subst sigma a in
      (* no need to substitute ts. *)
      (* all variables in ts are quantified existentially,
         so they cannot be the renamed variables. *)
      (* imprecise: they could initially have been the same as vars
         in the occ, but we forgot it.
         if we want to improve that, we'd need to only ex quantify the vars
         in ts not bound in the occ,
         but that's tricky, as it also means these vars can't be used
         to unify when subsuming timestamps *)
      let phi_time = 
        let path_cond =
          if use_path_cond then occ.eo_path_cond
          else PathCond.Top
        in
        rec_arg_formula ~path_cond table a f ts
      in
      if not negate then
        Term.mk_exists ~simpl:true fv
          (Term.mk_and  ~simpl:true phi_time phi_cond_cnt)
      else
        Term.mk_forall ~simpl:true fv
          (Term.mk_impl ~simpl:true phi_time phi_cond_cnt)

    | EI_direct -> (* direct occurrence *)
      if not negate then
        Term.mk_exists ~simpl:true fv phi_cond_cnt
      else
        Term.mk_forall ~simpl:true fv phi_cond_cnt
end 

(*------------------------------------------------------------------*)
(** Instantiation of all modules for searching name occurrences *)

(** Exported (see `.mli`) *)
module Name =
struct
  type t = { symb : Term.nsymb; args : Term.terms; }

  let subst (s : Term.subst) (n : t) : t =
    { n with args = List.map (Term.subst s) n.args }

  let pp ppe fmt (n : t) =
    if n.args = [] then
      Fmt.pf fmt "%a" Symbols.pp_path n.symb.s_symb
    else
      Fmt.pf fmt "%a(%a)"
        Symbols.pp_path n.symb.s_symb
        (Fmt.list ~sep:Fmt.comma (Term._pp ppe)) n.args

  let of_term : Term.term -> t = function
    | Name (symb, args) -> { symb; args; }
    | _ -> assert false

  let to_term { symb; args; } = Term.mk_name symb args

  let exists_name (n:t) (ns:t list) : bool =
    List.exists (fun nn -> n.symb.s_symb = nn.symb.s_symb) ns

  let find_name (n:t) (ns:t list) : t list =
    List.filter (fun nn -> n.symb.s_symb = nn.symb.s_symb) ns

  let rec has_name (n:t) (t:Term.term) : bool =
    match t with
    | Name (nn, _) when nn = n.symb -> true
    | _ -> Term.texists (has_name n) t

end

(*------------------------------------------------------------------*)
(** Exported (see `.mli`) *)
module NameOC : OccurrenceContent with type content = Name.t
                                   and type data = unit =
struct
  type content = Name.t
  type data = unit

  let collision_formula ~(negate : bool)
      ~(content : Name.t) ~(collision : Name.t) ~(data : unit)
    : Term.term =
    ignore data;
    (* sanity check: only apply when same symbol *)
    assert (content.symb = collision.symb);
    if not negate then
      Term.mk_eqs  ~simpl:true  ~simpl_tuples:true collision.args content.args
    else
      Term.mk_neqs ~simpl:false ~simpl_tuples:true collision.args content.args

  let subst_content = Name.subst

  let subst_data _ () = ()

  let pp_content = Name.pp

  let pp_data _ppe (fmt : Format.formatter) () : unit =
    Fmt.pf fmt ""
end

module NameOS = MakeSearch (NameOC)

module NameOF = MakeFormulas (NameOS.EO)

(*------------------------------------------------------------------*)
(** Exported (see `.mli`) *)
let find_name_occ (n:Name.t) (ns:Name.t list) (info:pos_info)
  : NameOS.simple_occs =
  List.map
    (fun (nn:Name.t) ->
       NameOS.EO.SO.mk_simple_occ
         ~content:n ~collision:nn ~data:()
         ~vars:info.pi_vars
         ~cond:info.pi_cond
         ~typ:info.pi_occtype
         ~sub:info.pi_subterm
         ~show:Show)
    (Name.find_name n ns)
