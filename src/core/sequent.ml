open Utils
open Ppenv

module L = Location
module SE = SystemExpr
module LS = LowSequent

module Sv = Vars.Sv
module Mvar = Match.Mvar

module HTerm = HighTerm

(*------------------------------------------------------------------*)
let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
module PT = struct
  (** A proof-term conclusion.
      For now, we do not keep the proof-term itself. *)
  type t = {
    system : SE.context;
      (** system wrt which everything is understood *)
    args   : (Vars.var * Vars.Tag.t) list;
      (** hole/pattern variables from applied terms
          (i.e. terms used to instantiate universal quantifications)
          in reversed order w.r.t. introduction *)
    mv     : Mvar.t;
      (** instantiations for metavariables resulting from
          instantiations of universal quantifications *)
      (* FIXME maintaining metavariables like this, using an
         explicit substitution rather than substituting eagerly,
         probably yields worse performance rather than a better
         one, because we substitute in several places during the
         construction of the proof term to avoid imprecision issues *)
    subgs  : Equiv.any_form list;
      (** subgoals *)
    bound  : Concrete.bound;
      (** concrete security bound *)
    form   : Equiv.any_form;
      (** conclusion of the proof term *)
  }

  let _pp ppe fmt (pt : t) : unit =
    let pp_subgoals_and_mv fmt =
      if not ppe.dbg then ()
      else
        Fmt.pf fmt "@[<v 2>subgoals:@ @[%a@]@]@;\
                    @[<v 2>mv:@ @[%a@]@]@;"
          (Fmt.list (Equiv.Any._pp ppe ?context:None))
          pt.subgs
          (Mvar._pp ppe) pt.mv
    in
    Fmt.pf fmt "@[<v 0>\
                %a judgement@;\
                formula: @[%a@]@;\
                @[system: @[%a@]@]@;\
                %t\
                @[vars: @[%a@]@]@]"
      (Concrete._pp ppe) pt.bound (* prints bound + judgement kind *)
      (Equiv.Any._pp ppe ?context:None) pt.form
      SE.pp_context pt.system
      pp_subgoals_and_mv
      (Vars._pp_typed_tagged_list ppe) (List.rev pt.args)

  let pp     = _pp (default_ppe ~dbg:false ())
  let pp_dbg = _pp (default_ppe ~dbg:true  ())

  (** Project the "set" part of a proof-terms's system annotations,
      and adjust reachability atoms accordingly,
      if this can be done while preserving the proof-term's validity.

      For instance, if a proof term establishes the local formula [f]
      under system annotation [{set:l1:P1,l2:P2;equiv:<E>}], projecting
      to [l1] results in a proof term establishing [f'] under the
      system annotation [{set:l1:P1;equiv:<E>}], where diff operators
      inside [f'] have been projected to [l1].

      We cannot always project so as to preserve validity:
      notably, it is generally unsound to project global hypotheses
      appearing in negative/contravariant positions.
      E.g. projecting over [P1] in
        [[phi]_{P1,P2} -> [psi]_{P1,P2}]
      would yield
        [[phi]_{P1} -> [psi]_{P1}]
      which is not implied by (and does not imply) the initial formula. *)
  let projs_set table env (projs : Projection.t list) (pt : t) : t =

    let system_independent env (f:Term.term) =
      let vars = Vars.add_vars pt.args env in
      let env = Env.init ~table ~system:pt.system ~vars () in
      (* Apply pending substitution to avoid imprecision. *)
      (* TODO un test pour ça FIXME genre lemma tau avec tau':=tau const *)
      let f =
        match Mvar.to_subst ~mode:`Unif table vars pt.mv with
        | `Subst subst -> Term.subst subst f
        | `BadInst _ -> f
          (* FIXME is it worth continuing, or should we fail now? *)
      in
      HTerm.is_system_indep env f
    in

    (** Check that reachability atoms appear
               only in positive positions when [b]
        (resp. only in negative positions when [not b])
        or are system independent. *)
    let rec check_positivity env (p : bool) (f : Equiv.form) =
      match f with
      | Quant (_,vars,f) -> check_positivity (Vars.add_vars vars env) p f
      | Let (_,_,f) -> check_positivity env p f
          (* FEATURE: enrich env with variable bound by Let,
             using tags inferred from second component. *)
      | And  (f1, f2)
      | Or   (f1, f2) -> check_positivity env p f1 && check_positivity env p f2
      | Impl (f1, f2) ->
        check_positivity env (not p) f1 &&
        check_positivity env      p  f2
      | Atom (Reach f) ->
        p || system_independent env f.formula
      | Atom _ -> true
    in

    let new_system = SE.project_set projs pt.system in

    let project_failure () =
      soft_failure (Failure "cannot project 'set' system annotation in proof-term")
    in

    (** [do_proj p form] returns a new formula [form'] such that
        [form] implies [form'] if [b], and conversely if [not b],
        where [form] is taken under the original system annotation
        and [form'] under the newly projected one.

        If will fail if system-dependent local formulas occur in
        negative occurrences; other occurrences will be projected
        to obtain [form'].

        FIXME explain (and check) what happens with equal_modulo:
        it seems that [l1:S,l2:S] equal_modulo [l1:S],
        but changing from one system to the other cannot be done
        without some conditions on occurrences. *)
    let do_proj (p : bool) : Equiv.any_form -> Equiv.any_form = function
      | Equiv.Local t ->
        let can_project =
          SE.equal_modulo table pt.system.set new_system.set ||
          p ||
          system_independent env t
        in
        if not can_project then project_failure ();
        Local (Term.project projs t)
      | Equiv.Global e ->
        (* If the system expressions after projection contains the
           same set of single systems, we can project. *)
        let can_project =
          SE.equal_modulo table pt.system.set new_system.set ||
          check_positivity env p e
        in
        if not can_project then project_failure ();
        Global (Equiv.project projs e)
    in

    { args   = pt.args;
      mv     = Match.Mvar.map (Term.project projs) pt.mv;
      system = new_system ;
      subgs  = List.map (do_proj false) pt.subgs;
      bound  = Concrete.bound_projs projs pt.bound;
      form   = do_proj true pt.form; }

end

(*------------------------------------------------------------------*)
(** Check that a proof-term is well-formed *)
let well_formed (pt : PT.t) : unit =
  begin (* check the bound *)
    match pt.form, pt.bound with
    | Global _, Concrete.Glob      -> ()
    | Global _, Concrete.LocHyp    -> assert false
    | Global _,                  _ -> assert false
    |        _, Concrete.Glob      -> assert false
    | Local  _, Concrete.LocAsym   -> ()
    | Local  _, Concrete.LocHyp    -> ()
    | Local  _, Concrete.LocConc _ -> ()
  end;

  begin (* check the subgoals *)
    match pt.form with
    | Global _ -> assert (List.for_all Equiv.is_global pt.subgs)
    | Local  _ -> ()
  end

(*------------------------------------------------------------------*)
(** Try to localize [pt] *)
let pt_try_localize ~(failed : unit -> PT.t) (pt : PT.t) : PT.t =
  let rec doit (pt : PT.t) : PT.t =
    match pt.form with
    | Local _ -> pt
    | Global (Atom (Reach f)) ->
      assert(pt.bound = Glob || pt.bound = LocAsym);
      let bound =
        if f.bound = None then Concrete.LocAsym else LocConc (oget f.bound)
      in
      { pt with form = Local f.formula; bound = bound }

    (* [pf_t] is a [forall vs, f]: add [vs] as variables *)
    | Global (Equiv.Quant (Equiv.ForAll, vs, f)) ->
      (* refresh variables *)
      let vs, subst = Term.refresh_vars_w_info vs in
      let f = Equiv.subst subst f in

      doit { pt with
             args = List.rev_append vs pt.args;
             form = Global f; }

    (* [pf_t] is an implication [f1 -> f2]: add [f1] as hypothesis *)
    | Global (Equiv.Impl (f1, f2)) ->
      doit { pt with
             subgs = Global f1 :: pt.subgs;
             form  = Global f2; }

    | Global _f -> failed ()

  in
  doit pt

(*------------------------------------------------------------------*)
(** Try to cast [pt] as a [dst] proof-term conclusion.
    Call [failed ()] in case of failure. *)
let pt_try_cast (type a)
    ~(failed : unit -> 'b)
    (dst : a Equiv.f_kind) (pt : PT.t) : PT.t
  =
  match dst, pt.form with
  | Equiv.Local_t , Local  _ -> pt
  | Equiv.Global_t, Global _ -> pt

  | Equiv.Local_t , Global _ -> well_formed pt; pt_try_localize ~failed pt

  | Equiv.Global_t, Local  _ -> failed ()
  (* Casting [pt.form] as a [Reach form] is generally unsound if [pt] has
     (discharged) local subgoals.
     Note that we could do such a cast if we first checked that there are
     no local subgoals. *)

  | Equiv.Any_t, _ -> pt

(*------------------------------------------------------------------*)

(** Return a new proof term equivalent to [pt] but using projections
    used in [system_pair] (which must be a projection renaming of [pt.system]).
    Diff operators in equivalence atoms are modified accordingly. *)
let pt_rename_system_pair (pt : PT.t) (system_pair : SE.pair option) : PT.t =
  match pt.system.pair, system_pair with
  | None, _ | _, None -> pt
  | Some pt_pair, Some system_pair ->
    (* Use [system_pair] projections in [pt], by renaming [pt]'s projections to
       projections in [system_pair] for the same single systems. *)
    let _, proj_subst =
      SE.mk_proj_subst ~strict:true
        ~src:(pt_pair :> SE.t) ~dst:(system_pair :> SE.t)
    in
    let psubst = Equiv.Babel.subst_projs Equiv.Any_t `Equiv proj_subst in
    let system =
      let pt_pair = SE.subst_projs proj_subst pt_pair in
      { pt.system with pair = Some pt_pair };
    in
    { pt with
      subgs = List.map psubst pt.subgs;
      form  = psubst pt.form;
      bound = Concrete.bound_subst_projs proj_subst pt.bound;
      system; }


(*------------------------------------------------------------------*)
(** Return a proof-term equivalent to [pt] but under the set annotation
    of [system], projecting diffs in reachability atoms if necessary.
    It is assumed that the change of annotation is possible, i.e. that
    enough checks have been performed before-hand.
    It is assumed (but not checked) that pair annotations require
    no changes to [pt]. *)
let pt_project_system_set
    (table : Symbols.table) (vars : Vars.env)
    (pt : PT.t) (system : SE.context) : PT.t
  =
  if pt.system = system then pt else
  (* project local hyps. and conclusion [arg] over [system]. *)
  if SE.is_fset system.set then
    if SE.is_fset pt.system.set then

      (* Use [system] projections in [pt], by renaming [pt]'s projections to
         projections in [system] for the same single systems. *)
      let _, proj_subst =
        SE.mk_proj_subst ~strict:true ~src:pt.system.set ~dst:system.set
      in
      let psubst = Equiv.Babel.subst_projs Equiv.Any_t `Reach proj_subst in
      let new_system =
        { pt.system with set = SE.subst_projs proj_subst pt.system.set }
      in
      let pt =
        { pt with subgs = List.map psubst pt.subgs;
                  bound = Concrete.bound_subst_projs proj_subst pt.bound;
                  (* FIXME shouldn't we subst_projs for mvars? *)
                  form  = psubst pt.form;
                  system = new_system }
      in

      (* [system] and [pt.system] are fsets.
         Project [pt] over [system.set]. *)
      let projs = List.map fst (SE.to_list @@ SE.to_fset system.set) in
      PT.projs_set table vars projs pt

    else
      (* [system.set] is a fset, [pt.system.set] is [SE.any]
         or [SE.any_compatible_with].
         In that case, no projection needed in terms: simply uses
         [system.set].
         FIXME don't we need to check polarities? e.g.
         if subgoal asks [input@tau=true] for all systems compatible
         with something, it's not OK to change it to weaker
         subgoal [input@tau=true]_{S}! *)
      let () = assert (SE.is_any pt.system.set) in
      { pt with system }
  else
    (* [system.set] is [SE.any] or [SE.any_compatible_with].
       [pt.system.set] must be in the same case.
       FIXME this is not what we check below *)
    let () = assert (SE.is_any    system.set &&
                     SE.is_any pt.system.set   ) in
    { pt with system }

(*------------------------------------------------------------------*)
let rec no_equiv (f : Equiv.form) : bool =
  match f with
  | Equiv.Atom (Equiv _) -> false
  | Equiv.Atom (Reach _) -> true
  | _ -> Equiv.tforall no_equiv f

let no_equiv_any : Equiv.any_form -> bool = function
  | Equiv.Local  _ -> true
  | Equiv.Global f -> no_equiv f

let is_system_context_indep : Equiv.any_form -> bool = function
  | Equiv.Local  _ -> false
  | Equiv.Global f -> Equiv.is_system_context_indep f

(*------------------------------------------------------------------*)
let pt_unify_warning_systems table ~(pt : PT.t) ~(arg : PT.t) : unit =
  let ppe = default_ppe ~table () in
  Printer.prt `Warning
    "Proof-term argument@;  @[%a@]@;\
     has less general systems than the proof-term it is applied into@;  \
     @[%a@]@;\
     The latter proof-term's system set has been projected."
    (PT._pp ppe) arg
    (PT._pp ppe) pt

(** Unify the systems of [pt] and [arg], prioritizing [pt]'s systems,
    projecting if necessary.
    Raise [failed] in case of failure. *)
let pt_unify_systems
    ~(failed : unit -> 'a)
    (table : Symbols.table)
    (vars  : Vars.env)
    ~(pt : PT.t) ~(arg : PT.t)
  : PT.t * PT.t
  =
  if List.for_all is_system_context_indep (arg.form :: arg.subgs) then
    pt, { arg with system = pt.system; }
  else if List.for_all is_system_context_indep (pt.form :: pt.subgs) then
    { pt with system = arg.system; }, arg
  else
    begin
      (* Check equivalence systems in [system.pair].
         Fails if not compatible. *)
      let arg_pair, pt_pair = arg.system.pair, pt.system.pair in
      if pt_pair <> None &&
         not (oequal (SE.equal_modulo table) pt_pair arg_pair)
      then
        failed ()
      else
        (* Unify projections of [system.pair] for [arg] and [pt]. *)
        let arg = pt_rename_system_pair arg pt_pair in

        (* Unify reachability systems in [system.set]. *)
        let pt_set, arg_set = pt.system.set, arg.system.set in
        (* FIXME subset_modulo used to be used below, but this yields
           projections from [l1:S] to [l1:S,l2:S], which is rejected:
           is there some generalization that we can/should do? *)
        if SE.subset table pt_set arg_set then
          pt, pt_project_system_set table vars arg pt.system
        else
        if SE.subset table arg_set pt_set then begin
          pt_unify_warning_systems table ~pt ~arg;
          pt_project_system_set table vars pt arg.system, arg
        end
        else failed ()
    end

(*------------------------------------------------------------------*)
(** {2 Module type for sequents} *)

type ghyp = [ `Hyp of Ident.t | `Lemma of string ]

module type S = sig
  include LowSequent.S

  (*------------------------------------------------------------------*)
  module Reduce : Reduction.S with type t := t

  (*------------------------------------------------------------------*)
  val is_assumption        : Symbols.p_path -> t -> bool
  val is_global_assumption : Symbols.p_path -> t -> bool
  val is_local_assumption  : Symbols.p_path -> t -> bool

  (*------------------------------------------------------------------*)
  val to_general_sequent : t -> Goal.t

  val to_global_sequent : t -> LowEquivSequent.t

  (*------------------------------------------------------------------*)
  val convert_pt_gen :
    check_compatibility:bool ->
    ?close_pats:bool ->
    Typing.pt ->
    t ->
    ghyp * Type.tvars * PT.t

  val convert_pt :
    ?close_pats:bool ->
    Typing.pt ->
    t ->
    ghyp * Type.tvars * PT.t
end

(*------------------------------------------------------------------*)
module type MkArgs = sig
  module S : LowSequent.S

  val to_general_sequent : S.t -> Goal.t
  val to_global_sequent  : S.t -> LowEquivSequent.t
end


module Mk (Args : MkArgs) : S with
  type t         = Args.S.t         and
  type conc_form = Args.S.conc_form and
  type hyp_form  = Args.S.hyp_form
= struct
  module S = Args.S
  include S

  let to_general_sequent = Args.to_general_sequent
  let to_global_sequent  = Args.to_global_sequent

  (*------------------------------------------------------------------*)
  let is_assumption (p : Symbols.p_path) (s : S.t) =
    (match p with ([],name) -> Hyps.mem_name (L.unloc name) s | _ -> false) ||
    Lemma.mem p (S.table s)

  let is_global_assumption (p : Symbols.p_path) (s : sequent) =
    (match p with ([],name) -> Hyps.mem_name (L.unloc name) s | _ -> false) ||
    Lemma.mem_global p (S.table s)

  let is_local_assumption (p : Symbols.p_path) (s : sequent) =
    (match p with ([],name) -> Hyps.mem_name (L.unloc name) s | _ -> false) ||
    Lemma.mem_local p (S.table s)

  (*------------------------------------------------------------------*)
  let destr_impl_k
      (type a)
      (f_kind : a Equiv.f_kind)
      (env : Env.t)
      (f   : a)
    : (a * a) option
    =
    match f_kind with
    | Equiv.Local_t  -> HTerm.Smart.destr_impl ~env f
    | Equiv.Global_t -> Equiv.Smart.destr_impl ~env f
    | Equiv.Any_t ->
      match f with
      | Local f ->
        omap
          (fun (v,f) -> Equiv.Local v, Equiv.Local f)
          (HTerm.Smart.destr_impl ~env f)

      | Global f ->
        omap
          (fun (v,f) -> Equiv.Global v, Equiv.Global f)
          (Equiv.Smart.destr_impl ~env f)

  let destr_forall1_tagged_k
      (type a)
      (f_kind : a Equiv.f_kind)
      (f      : a)
    : (Vars.tagged_var * a) option
    =
    match f_kind with
    | Equiv.Local_t  -> HTerm.Smart.destr_forall1_tagged f
    | Equiv.Global_t -> Equiv.Smart.destr_forall1_tagged f

    | Equiv.Any_t ->
      match f with
      | Local f ->
        omap
          (fun (v,f) -> v, Equiv.Local f)
          (HTerm.Smart.destr_forall1_tagged f)

      | Global f ->
        omap
          (fun (v,f) -> v, Equiv.Global f)
          (Equiv.Smart.destr_forall1_tagged f)

  let decompose_forall_tagged_k
      (type a)
      (f_kind : a Equiv.f_kind)
      (f      : a)
    : Vars.tagged_vars * a
    =
    match f_kind with
    | Equiv.Local_t  -> HTerm.Smart.decompose_forall_tagged f
    | Equiv.Global_t -> Equiv.Smart.decompose_forall_tagged f

    | Equiv.Any_t ->
      match f with
      | Local f ->
        let vs,f = HTerm.Smart.decompose_forall_tagged f in
        vs, Local f

      | Global f ->
        let vs,f = Equiv.Smart.decompose_forall_tagged f in
        vs, Global f

  (*------------------------------------------------------------------*)
  (** Return the location of a proof term argument. *)
  let pt_arg_loc (p_arg : Typing.pt_app_arg) : L.t =
    match p_arg with
    | PTA_term  t -> L.loc t
    | PTA_sub  pt -> L.loc pt

  let pt_app_arg_as_term (p_arg : Typing.pt_app_arg) : Typing.term =
    match p_arg with
    | Typing.PTA_term t -> t
    | _ ->
      hard_failure ~loc:(pt_arg_loc p_arg) (Failure "expected a term")

  (** A proof term with type [f1 -> f2] argument is either:
      - another proof term whose type [f'] must match [f1]
      - an underscore, which generates a subgaol for [f1] *)
  type pt_impl_arg = [`Pt of Typing.pt | `Subgoal]

  (** Try to interpret a proof term argument as a proof term. *)
  let pt_app_arg_as_pt
    (p_arg : Typing.pt_app_arg) : [`Pt of Typing.pt | `Subgoal]
  =
    match p_arg with
    | Typing.PTA_sub pt -> `Pt pt

    (* if we gave a term, re-interpret it as a proof term *)
    | Typing.PTA_term ({ pl_desc = Symb (head, ty_args) } as t)
    | Typing.PTA_term
        ({ pl_desc = App ({ pl_desc = Symb (head, ty_args) }, _) } as t) ->
      let _head, terms = Typing.decompose_app t in (* [_head = head] *)
      let loc = L.loc t in

      let pt_cnt =
        Typing.PT_app {
          pta_head =
            L.mk_loc (Symbols.p_path_loc head) (Typing.PT_symb (head, ty_args));
          pta_args = List.map (fun x -> Typing.PTA_term x) terms ;
          pta_loc  = loc;
        }
      in
      `Pt (L.mk_loc loc pt_cnt)

    | Typing.PTA_term { pl_desc = Typing.Tpat } -> `Subgoal

    | _ ->
      hard_failure ~loc:(pt_arg_loc p_arg) (Failure "expected a term")

  (*------------------------------------------------------------------*)
  let error_pt_nomatch loc table ~(prove : PT.t) ~(target : PT.t) =
    let ppe = default_ppe ~table () in
    let err_str =
      Fmt.str "@[<v 0>the proof term proves:@;  \
               @[%a@]@;\
               but it must prove:@;  \
               @[%a@]@]"
        (PT._pp ppe) prove
        (PT._pp ppe) target
    in
    soft_failure ~loc (Failure err_str)

  (*------------------------------------------------------------------*)
  let error_pt_wrong_number_ty_args
    loc ~(expected : Type.ty list) ~(got : Type.ty list)
  =
    let err_str =
      Fmt.str "@[<v 0>wrong number of type variables: \
               expected %d, got %d@]"
        (List.length expected) (List.length got)
    in
    soft_failure ~loc (Failure err_str)

  (*------------------------------------------------------------------*)
  (** Auxiliary function building a location for nice errors. *)
  let last_loc (head_loc : L.t) (args : 'a L.located list) : L.t =
    let exception Fail in
    let end_loc =
      try
        let last = List.last ~e:Fail args in
        L.loc last
      with Fail -> head_loc
    in
    L.merge head_loc end_loc


  (** Solve parser ambiguities, e.g. in [H (G x)], the sub-element [(G x)] is
      parsed as a term (i.e. a [PTA_term]. We resolve it as a [PTA_sub] using
      the context. *)
  let rec resolve_pt_arg
    (s : S.t) (pt_arg : Typing.pt_app_arg) : Typing.pt_app_arg
  =
    match pt_arg with
    | Typing.PTA_sub sub -> PTA_sub (resolve_pt s sub)
    | Typing.PTA_term t  ->
      match L.unloc t with
      | Typing.App ({ pl_desc = Typing.Symb (([],h), ty_args) }, args)
        when S.Hyps.mem_name (L.unloc h) s
        ->
        if ty_args <> None then
          hard_failure ~loc:(L.loc t) (Failure "unexpected type arguments");

        let pta_args =
          List.map (fun a -> resolve_pt_arg s (Typing.PTA_term a)) args
        in
        let loc = last_loc (L.loc h) args in
        let pt_cnt =
          Typing.PT_app {
            pta_head = L.mk_loc (L.loc h) (Typing.PT_symb (([],h), None));
            pta_args;
            pta_loc = loc;
          }
        in
        PTA_sub (L.mk_loc loc pt_cnt)

      | _ -> pt_arg

  and resolve_pt (s : S.t) (pt : Typing.pt) : Typing.pt =
    let loc = L.loc pt in
    match L.unloc pt with
    | PT_symb _ -> pt

    | PT_localize sub_pt ->
      L.mk_loc loc (Typing.PT_localize (resolve_pt s sub_pt))

    | PT_app app ->
      let app =
        Typing.{ app with pta_args = List.map (resolve_pt_arg s) app.pta_args }
      in
      L.mk_loc loc (Typing.PT_app app)

  (*------------------------------------------------------------------*)
  (** Internal
      Get a proof-term conclusion by name (from a lemma, axiom or hypothesis).
      Optionally apply it to some user-provided type arguments. *)
  let pt_of_assumption
      (ty_env   : Infer.env)
      (p        : Symbols.p_path)
      (ty_args  : Type.ty list option)
      (s        : t)
    : ghyp * PT.t
    =
    let top, sub = fst p, snd p in
    if top = [] && Hyps.mem_name (L.unloc sub) s then
      let id, f = Hyps.by_name_k sub Hyp s in
      let g : (Equiv.any_form * Concrete.bound) =
        match S.hyp_kind with
        | Equiv.Any_t -> f, if Equiv.is_local f then Concrete.LocHyp else Glob
        | Equiv.Local_t as src ->
          Equiv.Babel.convert ~loc:(L.loc sub) ~src ~dst:Equiv.Any_t f, LocHyp
        | Equiv.Global_t as src ->
          Equiv.Babel.convert ~loc:(L.loc sub) ~src ~dst:Equiv.Any_t f, Glob
      in
      let f, bound = g in

      `Hyp id,
      { system = S.system s;
        subgs  = [];
        mv     = Mvar.empty;
        args   = [];
        bound= bound;
        form   = f; }

    else
      let lem =
        try Lemma.find_stmt p (S.table s) with
        | Symbols.Error (_, Symbols.Unbound_identifier _) ->
          soft_failure ~loc:(Symbols.p_path_loc p)
            (Failure ("no lemma named " ^ Symbols.p_path_to_string p))
      in

      (* Open the lemma type variables. *)
      let ty_vars, tsubst = Infer.open_tvars ty_env lem.ty_vars in

      (* if the user provided type variables, apply them *)
      if ty_args <> None then
        begin
          let ty_args = oget ty_args in
          let ty_vars = List.map (fun u -> Type.univar u) ty_vars in

          if List.length ty_args <> List.length ty_vars then
            error_pt_wrong_number_ty_args
              (Symbols.p_path_loc p) ~expected:ty_vars ~got:ty_args;

          List.iter2
            (fun ty1 ty2 ->
               match Infer.unify_eq ty_env ty1 ty2 with
               | `Ok   -> ()
               | `Fail -> assert false) (* cannot fail *)
            ty_vars ty_args;
        end;

      let form = Equiv.Babel_statement.gsubst Equiv.Any_s tsubst lem.formula in
      if Equiv.is_local_statement form
      then
        (* a local lemma or axiom is actually a global reachability formula *)
        let form, bound =
          match S.conc_kind, form with
          (* we already downgraded it for local sequents *)
          | Equiv.Local_t, Equiv.LocalS {formula; bound = Some ve } ->
            Equiv.Local formula, Concrete.LocConc ve

          | Equiv.Local_t, Equiv.LocalS {formula; bound = None    } ->
            Equiv.Local formula, Concrete.LocAsym

          (* in global sequent, we use it as a global formula  *)
          | Equiv.Global_t, Equiv.LocalS f ->
            Equiv.Global (Atom (Reach f)), Glob

          | _ -> assert false (* impossible *)
        in

        `Lemma lem.Goal.name,
        { system = lem.system;
          mv     = Mvar.empty;
          subgs  = [];
          args   = [];
          bound;
          form; }
      else
      (* a local lemma or axiom is actually a global reachability formula *)
      let form =
        match S.conc_kind, form with
        (* we already downgrade it for local sequents *)
        | Equiv.Local_t, Equiv.GlobalS f -> Equiv.Global f
        (* in global sequent, we use it as a global formula  *)
        | Equiv.Global_t, Equiv.LocalS f -> Equiv.Global (Atom (Reach f))
        | Equiv.Global_t, Equiv.GlobalS f -> Equiv.Global f
        | _  -> assert false (* impossible *)
      in

        `Lemma lem.Goal.name,
        { system = lem.system;
          mv     = Mvar.empty;
          subgs  = [];
          args   = [];
          bound = Glob;
          form; }

  (*------------------------------------------------------------------*)
  (** Extend a variable environment with the variables of [pt] *)
  let venv_of_pt (env : Vars.env) (pt : PT.t) : Vars.env =
    Vars.add_vars pt.args env

  (** Extend an environment with the variables of [pt] *)
  let env_of_pt table system (env : Vars.env) (pt : PT.t) : Env.t =
    Env.init ~table ~system ~vars:(venv_of_pt env pt) ()

  (*------------------------------------------------------------------*)
  let error_pt_apply_not_system_indep table loc ~(pt : PT.t) ~(arg : Term.t) =
    let ppe = default_ppe ~table () in
    let err_str =
      Fmt.str "@[<v 0>The term:@;  @[%a@]@;\
               is not system-independent. \
               It cannot be applied to:@;  @[%a@].@]"
        (Term._pp ppe) arg
        (PT._pp   ppe) pt
    in
    soft_failure ~loc (Failure err_str)

  (*------------------------------------------------------------------*)
  let error_pt_apply_not_adv table loc ~(pt : PT.t) ~(arg : Term.t) =
    let ppe = default_ppe ~table () in
    let err_str =
      Fmt.str "@[<v 0>The term:@;  @[%a@]@;\
               is not computable by the adversary. \
               It cannot be applied to:@;  @[%a@].@]"
        (Term._pp ppe) arg
        (PT._pp   ppe) pt
    in
    soft_failure ~loc (Failure err_str)

    (*------------------------------------------------------------------*)
  let error_pt_apply_not_constant table loc ~(pt : PT.t) ~(arg : Term.t) =
    let ppe = default_ppe ~table () in
    let err_str =
      Fmt.str "@[<v 0>The term:@;  @[%a@]@;\
               is not constant. It cannot be applied to:@;  @[%a@].@]"
        (Term._pp ppe) arg
        (PT._pp   ppe) pt
    in
    soft_failure ~loc (Failure err_str)

  (*------------------------------------------------------------------*)
  (** Apply proof-term ([PT.t]) to some term ([Term.term]):
      pop the first universally quantified variable in the proof-term's
      conclusion and instantiate it with given term. *)
  let pt_apply_var_forall
      ~(arg_loc:L.t)
      (ty_env : Infer.env)
      (table : Symbols.table) (env : Vars.env)
      (pt : PT.t) (pt_arg : Term.term)
    : PT.t
    =
    let (f_arg, f_arg_tag), f =
      oget (destr_forall1_tagged_k Equiv.Any_t pt.form) in

    (* refresh the variable *)
    let f_arg, fs = Term.refresh_vars [f_arg] in
    let f = Equiv.Any.subst fs f in
    let f_arg = as_seq1 f_arg in

    (* collect hole vars in the argument [pt_arg] *)
    let new_p_vs = Sv.filter Vars.is_pat (Term.fv pt_arg) in
    (* hole vars are global if [pt]'s conclusion is a global quant., i.e.
       if [f_arg_kind] is [`Global]. *)
    let args =
      List.rev_append
        (List.map (fun x -> x, f_arg_tag) (Sv.elements new_p_vs))
        pt.args
    in

    (* check tags, if applicable *)
    (* FIXME factor this behind a central function call,
       otherwise we might forget to update this code after adding a new tag *)
    let () =
      let venv = Vars.add_vars args env in
      let env = Env.init ~table ~system:pt.system ~vars:venv () in

      if f_arg_tag.system_indep &&
         not (HTerm.is_single_term_in_context ~context:env.system env pt_arg) then
        error_pt_apply_not_system_indep table arg_loc ~pt ~arg:pt_arg;
      (* TODO: multi-terms: this check probably needs to modified *)

      if
        f_arg_tag.adv && not (HTerm.is_ptime_deducible ~si:false env pt_arg)
      then
        error_pt_apply_not_adv table arg_loc ~pt ~arg:pt_arg;

      if f_arg_tag.const && not (HTerm.is_constant ~ty_env env pt_arg) then
        error_pt_apply_not_constant table arg_loc ~pt ~arg:pt_arg;
    in

    let mv =
      Mvar.add (f_arg, f_arg_tag) pt.system.set pt_arg pt.mv
    in
    { subgs = pt.subgs; args; mv; form = f;
      bound = pt.bound; system = pt.system }

  (*------------------------------------------------------------------*)
  let pt_downgrade_warning table ~(pt : PT.t) ~(arg : PT.t) : unit =
    let ppe = default_ppe ~table () in
    Printer.prt `Warning
      "Proof-term argument@;  @[%a@]@;\
       is local, while the proof-term it is applied into is global@;  @[%a@]@;\
       The latter proof-term has been downgraded to a local proof-term."
      (PT._pp ppe) arg
      (PT._pp ppe) pt

  (*------------------------------------------------------------------*)
  let error_pt_apply_bad_kind loc table ~(pt : PT.t) ~(arg : PT.t) =
    let ppe = default_ppe ~table () in
    let err_str =
      Fmt.str "@[<v 0>bad kind: the proof term proves:@;  @[%a@]@;\
               it cannot be applied to:@;  @[%a@].@]"
        (PT._pp ppe) arg
        (PT._pp ppe) pt
    in
    soft_failure ~loc (Failure err_str)

  (*------------------------------------------------------------------*)
  let error_pt_apply_asymptotic_concrete () =
    soft_failure
      (Failure "cannot apply a concrete implication \
                with an asymptotic hypothesis")

   (*------------------------------------------------------------------*)
  let subst_of_pt ~loc ty_env table (vars : Vars.env) (pt : PT.t) : Term.subst =
    let pt_venv = venv_of_pt vars pt in
    match Mvar.to_subst ~ty_env ~mode:`Unif table pt_venv pt.mv with
    | `Subst sbst -> sbst
    | `BadInst pp_err ->
      soft_failure ~loc
        (Failure (Fmt.str "@[<hv 2>proof-term failed:@ @[%t@]@]" pp_err))

  (*------------------------------------------------------------------*)
  (** Apply [pt] to [arg] when [pt] is an implication.
      Pop the first implication [f1] of [pt.form], instantiate (by matching) it
      using [arg], and return the updated [pt].

      Remark: [arg]'s substitution must be an extention of
      [pt]'s substitution. *)
  let pt_apply_var_impl
      (* ~(loc : L.t)  *) ~(loc_arg : L.t)
      (ty_env : Infer.env) (s : S.t)
      (pt : PT.t) (arg : PT.t)
    : PT.t
    =
    let table = S.table s in

    let apply_kind_error () = error_pt_apply_bad_kind loc_arg table ~pt ~arg in

    (* Try to case [arg] to the appropriate kind (local or global),
       depending on [f1] kind.
       If the cast fails, we raise a user-level error. *)
    let pt, arg =
      match pt.form, arg.form with
      | Equiv.Local  _, Equiv.Local  _
      | Equiv.Global _, Equiv.Global _ -> pt, arg
      | Equiv.Local  _, Equiv.Global _ ->
        (* downgrade [arg] *)
        let down_arg = pt_try_localize ~failed:apply_kind_error arg in
        pt, down_arg

      | Equiv.Global _, Equiv.Local  _ ->
        (* downgrade [pt] *)
        let down_pt = pt_try_localize ~failed:apply_kind_error pt in
        pt_downgrade_warning table ~pt ~arg;
        down_pt, arg
    in

    let f1, f2 =
      let pt_env = env_of_pt (S.table s) (S.system s) (S.vars s) pt in
      oget (destr_impl_k Equiv.Any_t pt_env pt.form)
    in
    (* Specializing [pt.form] by an extention of [pt.mv]. *)
    (* FIXME: correct location? *)
    let sbst = subst_of_pt ~loc:loc_arg ty_env table (S.vars s) arg in
    let f1 = Equiv.Any.subst sbst f1 in
    let pat_f1 = Term.{
        pat_op_vars   = pt.args;
        pat_op_term   = f1;
        pat_op_tyvars = [];
      } in

    let pt_apply_error arg () =
      error_pt_nomatch loc_arg table ~prove:arg ~target:{ pt with form = f1 }
    in

    (* Verify that the systems of the argument [arg] applies to the systems
       of [pt], projecting it if necessary. *)
    let pt, arg =
      pt_unify_systems ~failed:(pt_apply_error arg) table (S.vars s) ~pt ~arg
    in

    let match_res =
      (* variable environment with both [pt] and [arg] variables
         (with their tags). *)
      let env = Vars.add_vars (arg.args @ pt.args) (S.vars s) in

      match f1, arg.form with
      | Local f1, Local f_arg ->
        let pat_f1 = { pat_f1 with pat_op_term = f1 } in
        Match.T.try_match
          ~ty_env ~mv:arg.mv ~env
          table pt.system f_arg pat_f1

      | Global f1, Global f_arg  ->
        assert(pt.bound = Glob && arg.bound = Glob);
        let pat_f1 = { pat_f1 with pat_op_term = f1 } in
        Match.E.try_match
          ~ty_env ~mv:arg.mv ~env
          table pt.system f_arg pat_f1

      | _ -> assert false       (* impossible thanks to [pt_try_localize] *)
    in
    let mv = match match_res with
      | Match.NoMatch _  -> pt_apply_error arg ()
      | Match.Match   mv -> mv
    in

    (* Add to [pt.args] the new variables that must be instantiated in
       the proof term [p_arg]. *)
    let args = List.rev_append arg.args pt.args in
    let subgs = arg.subgs @ pt.subgs in
    let bound =
      match pt.bound, arg.bound with
      | LocConc b, LocConc sb ->
        Concrete.LocConc
          (Library.Real.mk_add table sb (Library.Real.mk_opp table b))
      | f, g when Concrete.equal f g  -> f
      | LocAsym  , LocHyp    -> LocAsym
      | LocHyp   , LocAsym   -> LocAsym
      | LocHyp   , LocConc _ -> arg.bound
      | LocConc _, LocHyp    -> pt.bound
      | _ -> error_pt_apply_asymptotic_concrete ()
    in
    { subgs; mv; args; form = f2; bound; system = pt.system; }

  (*------------------------------------------------------------------*)
  let error_pt_cannot_apply loc table (pt : PT.t) =
    let ppe = default_ppe ~table () in
    let err_str =
      Fmt.str "@[<hov 2>too many argument, cannot apply:@;  @[%a@]@]"
        (PT._pp ppe) pt
    in
    soft_failure ~loc (Failure err_str)

  (*------------------------------------------------------------------*)
  let error_pt_cannot_localize loc table (pt : PT.t) () =
    let ppe = default_ppe ~table () in
    let err_str =
      Fmt.str "@[<v 0>cannot localize the proof term:@;  @[%a@]@;@]"
        (PT._pp ppe) pt
    in
    soft_failure ~loc (Failure err_str)

  (*------------------------------------------------------------------*)
  (** Parse a partially applied lemma or hypothesis as a pattern. *)
  let rec do_convert_pt_gen
      (ty_env : Infer.env)
      (mv : Mvar.t)
      (p_pt : Typing.pt)
      (s : S.t) : ghyp * PT.t
    =
    let table = S.table s in
    let ghyp, pt =
      match L.unloc p_pt with
      | Typing.PT_symb (path, ty_args) ->
        do_convert_path ty_env mv path ty_args s
      | Typing.PT_app pt_app -> do_convert_pt_app ty_env mv pt_app s
      | Typing.PT_localize p_sub_pt ->
        let ghyp, sub_pt = do_convert_pt_gen ty_env mv p_sub_pt s in
        let pt =
          pt_try_localize
            ~failed:(error_pt_cannot_localize (L.loc p_sub_pt) table sub_pt)
            sub_pt
        in
        ghyp, pt
    in
    well_formed pt;             (* sanity check *)
    ghyp, pt

  and do_convert_path
      (ty_env  : Infer.env)
      (init_mv : Mvar.t)
      (p       : Symbols.p_path)
      (ty_args : Typing.ty list option)
      (s       : S.t)
    : ghyp * PT.t
    =
    let ty_args =
      omap (List.map (Typing.convert_ty ~ty_env (S.env s))) ty_args
    in
    let lem_name, pt = pt_of_assumption ty_env p ty_args s in
    assert (pt.mv = Mvar.empty);
    let pt = { pt with mv = init_mv; } in
    lem_name, pt

  and do_convert_pt_app
      (ty_env  : Infer.env)
      (init_mv : Mvar.t)
      (pt_app  : Typing.pt_app)
      (s       : S.t)
    : ghyp * PT.t
    =
    let table, env = S.table s, S.vars s in

    let lem_name, init_pt =
      do_convert_pt_gen ty_env init_mv pt_app.pta_head s
    in

    let cenv = Typing.{ env = S.env s; cntxt = InGoal; } in

    (** Apply [pt] to [p_arg] when [pt] is a forall. *)
    let do_var (pt : PT.t) (p_arg : Typing.term) : PT.t =
      match destr_forall1_tagged_k Equiv.Any_t pt.form with
      | None ->
        error_pt_cannot_apply (L.loc pt_app.pta_head) table pt

      | Some ((f_arg, _), _) ->
        let ty = Vars.ty f_arg in
        let arg, _ = Typing.convert ~ty_env ~pat:true cenv ~ty p_arg in

        pt_apply_var_forall ~arg_loc:(L.loc p_arg) ty_env table env pt arg
    in

    (** Apply [pt] to [p_arg] when [pt] is an implication. *)
    let do_impl
        (ty_env : Infer.env)
        (pt : PT.t) (pt_impl_arg : pt_impl_arg)
      : PT.t
      =
      let pt_env = env_of_pt (S.table s) (S.system s) (S.vars s) pt in

      (* try to destruct [pt.form] as an implication *)
      let f1, f2 =
        match destr_impl_k Equiv.Any_t pt_env pt.form with
        | Some (f1, f2) -> f1, f2
        | None ->
          (* destruct failed, applying the pending substitution and try to
             destruct again *)
          let subst =
            subst_of_pt ~loc:pt_app.pta_loc ty_env table (S.vars s) pt in
          match
            destr_impl_k Equiv.Any_t pt_env (Equiv.Any.subst subst pt.form)
          with
          | Some (f1, f2) -> f1, f2
          | None ->
            error_pt_cannot_apply (L.loc pt_app.pta_head) table pt
      in

      match pt_impl_arg with
      | `Subgoal ->             (* discharge the subgoal *)
        { PT.system = pt.system;
          subgs  = f1 :: pt.subgs;
          mv     = pt.mv;
          args   = pt.args;
          bound  = pt.bound;
          form   = f2; }

      | `Pt p_arg ->
        let _, pt_arg = do_convert_pt_gen ty_env pt.mv p_arg s in
        pt_apply_var_impl
          ~loc_arg:(L.loc p_arg)
          ty_env s
          pt pt_arg
    in

    (* fold through the provided arguments and [f],
       instantiating [f] along the way,
       and accumulating proof obligations. *)
    let pt =
      List.fold_left (fun (pt : PT.t) (p_arg : Typing.pt_app_arg) ->
          if destr_forall1_tagged_k Equiv.Any_t pt.form = None then
            do_impl ty_env pt (pt_app_arg_as_pt p_arg)
          else
            do_var pt (pt_app_arg_as_term p_arg)
        ) init_pt pt_app.pta_args
    in

    lem_name, pt

  (*------------------------------------------------------------------*)
  (** Closes inferred variables from [pt.args] by [pt.mv]. *)
  let close
      (loc : L.t)
      (ty_env : Infer.env) (table : Symbols.table) (env : Vars.env)
      (pt : PT.t) : PT.t
    =
    (* clear infered variables from [pat_vars] *)
    let args =
      List.filter (fun (v, _) -> not (Mvar.mem v pt.mv)) pt.args
    in
    (* instantiate infered variables *)
    (* FIXME why don't we substitute in [pt.bound]? *)
    let subst = subst_of_pt ~loc ty_env table env pt in
    let form = Equiv.Any.subst subst pt.form in
    let subgs = List.map (Equiv.Any.subst subst) pt.subgs in
    (* the only remaining variables are pattern holes '_' *)
    assert (List.for_all (fst_map Vars.is_pat) args);

    (* rename remaining pattern variables,
       to avoid having variables named '_' in the rest of the prover. *)
    let subst, args =
      List.map_fold (fun subst (v, var_info) ->
          let new_v = Vars.make_fresh (Vars.ty v) "x" in
          let subst = Term.ESubst (Term.mk_var v, Term.mk_var new_v) :: subst in
          ( subst,
            (new_v, var_info) )
          ) [] args
    in
    let form = Equiv.Any.subst subst form in
    let subgs = List.map (Equiv.Any.subst subst) subgs in
    { pt with mv = Mvar.empty; subgs; args; form; }

  (*------------------------------------------------------------------*)
  let error_pt_bad_system loc table (pt : PT.t) =
    let ppe = default_ppe ~table () in
    let err_str =
      Fmt.str "@[<v 0>the proof term proves:@;  @[%a@]@;\
               it does not apply to the current system.@]"
        (PT._pp ppe) pt
    in
    soft_failure ~loc (NoAssumpSystem err_str)

  (*------------------------------------------------------------------*)
  (** Exported. *)
  let convert_pt_gen
      ~check_compatibility
      ?(close_pats=true)
      (p_pt : Typing.pt)
      (s    : S.t)
    : ghyp * Type.tvars * PT.t
    =
    let table = S.table s in
    (* resolve (to some extent) parser ambiguities in [s] *)
    let p_pt = resolve_pt s p_pt in
    let loc = L.loc p_pt in

    (* create a fresh unienv and matching env *)
    let ty_env = Infer.mk_env () in
    let mv = Mvar.empty in

    (* convert the proof term *)
    let name, pt = do_convert_pt_gen ty_env mv p_pt s in

    let pt =
      if not check_compatibility then
        pt
      else if List.for_all is_system_context_indep (pt.form :: pt.subgs) then
        (* TODO this case seems hardly useful because [is_system_context_indep]
           currently forbids both reach and equiv atoms *)
        { pt with system = S.system s }
      else

        (* First adjust proof-term wrt pair annotation.
           Annotation will be changed later. *)
        let pt =
          match pt.system.pair, (S.system s).pair with

          (* Cases where annotation is irrelevant. *)
          | None, _ -> pt
          | Some _, _ when List.for_all no_equiv_any (pt.form :: pt.subgs) -> pt

          (* Same pair annotations, i.e. same systems with same labels. *)
          | Some src, Some dst when SE.equal table src dst -> pt

          (* Swapped systems. *)
          | Some src, Some dst
            when
              let (_,src1),(_,src2) = SystemExprSyntax.fst src, SystemExprSyntax.snd src in
              let (_,dst1),(_,dst2) = SystemExprSyntax.fst dst, SystemExprSyntax.snd dst in
              (src1,src2) = (dst2,dst1) ->
            pt_rename_system_pair pt (Some dst)

          | _ -> error_pt_bad_system loc table pt
        in

        (* Then adjust proof-term for set annotations. *)
        if SE.is_any pt.system.set then { pt with system = S.system s } else
        let pt_set = SE.(to_list (to_fset pt.system.set)) in
        let s_set = SE.(to_list (to_fset (S.system s).set)) in
        (* We want to be able to move from a set annotation to one of its
           subsets (e.g. from [left:S1,right:S2] to [left:S1]) but we also
           want to be able to rename projections (e.g. going from
           [left:S1,right:S2] to [epsilon:S1]).
           It is however not safe to use pt_project_system_set when the target
           set annotation is a subset_modulo of the original annotation:
           we have to guarantee that mk_proj_subst does not encounter
           conflicting projections. Hence we check below a criterion that
           sits somewhere between subset and subset_modulo.
           In addition to this, we handle separately a special case,
           which allows to move e.g. from [left:S1,right:S2] to
           [lbl1:S1,lbl2:S1], as this is easily achieved and is used in
           one of our examples (although it was probably initially only
           supported by accident). *)
        match s_set with
        | (lbl,ss)::tl when
          List.exists (fun (_,ss') -> ss = ss') pt_set &&
          List.for_all (fun (_,ss') -> ss = ss') tl ->
          (* Project to ss alone, then move to repeated set annotation,
             which is logically equivalent and requires no modification
             of terms as diff operators cannot appear. *)
          let pt =
            pt_project_system_set table (S.vars s) pt
              { (S.system s) with set = (SE.make_fset table ~labels:[Some lbl] [ss] :> < > SE.expr) }
          in
          { pt with system = S.system s }
        | _ ->
          (* Every single system in s_set must be covered (perhaps ambiguously)
             by a single system from pt_set, and every single system from
             pt_set should correspond to at most one single system in s_set so
             that projection renaming is a function. *)
          if List.for_all
               (fun (_,sys) ->
                  let l = List.filter (fun (_,sys') -> sys = sys') pt_set in
                  List.length l >= 1)
               s_set &&
             List.for_all
               (fun (_,sys) ->
                 let l = List.filter (fun (_,sys') -> sys = sys') s_set in
                 List.length l <= 1)
               pt_set
          then
            pt_project_system_set table (S.vars s) pt (S.system s)
          else
            error_pt_bad_system loc table pt
    in

    (* close proof-term by inferring as many pattern variables as possible *)
    let pt = close loc ty_env table (S.vars s) pt in
    assert (pt.mv = Mvar.empty);

    (* pattern variable remaining, and not allowed *)
    if close_pats && not (pt.args = []) then
      Tactics.soft_failure Tactics.CannotInferPats;

    (* close the unienv and generalize remaining univars *)
    let pat_tyvars, tysubst = Infer.gen_and_close ty_env in
    let form = Equiv.Babel.gsubst Equiv.Any_t tysubst pt.form in
    let subgs = List.map (Equiv.Babel.gsubst Equiv.Any_t tysubst) pt.subgs in
    let args =
      List.map (fun (v, info) -> Subst.subst_var tysubst v, info) pt.args in

    (* generalize remaining universal variables in f *)
    (* FIXME: don't generalize in convert_pt_gen *)
    let f_args, form = decompose_forall_tagged_k Equiv.Any_t form in
    let f_args, subst = Term.refresh_vars_w_info f_args in

    let form = Equiv.Any.subst subst form in
    let args = List.append f_args args in

    let pt = { pt with form; subgs; args; } in

    name, pat_tyvars, pt

  (*------------------------------------------------------------------*)
  (** Exported. *)
  let convert_pt
      ?close_pats
      (pt :  Typing.pt)
      (s : S.t)
    : ghyp * Type.tvars * PT.t
    =
    let name, tyvars, pt =
      convert_pt_gen ~check_compatibility:true ?close_pats pt s
    in
    name, tyvars, pt

  (*------------------------------------------------------------------*)
  module Reduce = Reduction.Mk(S)
end
