open Utils

module L = Location
module SE = SystemExpr
module LS = LowSequent

module Sv = Vars.Sv
module Mvar = Match.Mvar

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
module PT = struct
  (** A proof-term conclusion.
      For now, we do not keep the proof-term itself. *)
  type t = {
    system : SE.context;
    args   : Sv.t;
    mv     : Mvar.t;
    subgs  : Equiv.any_form list;
    form   : Equiv.any_form;
  }

  (** Project the [set] of all systems in a proof-term. *)
  let projs_set_in_local (projs : Term.projs) (pt : t) : t =
    (* It does not make sense to project global hypotheses.
       E.g. projecting over [P1] in
         [phi]_{P1,P2} -> [psi]_{P1}
       would yield
         [phi]_{P1} -> [psi]_{P1} 
       which is stronger than the initial formula.*)
    let do_proj : Equiv.any_form -> Equiv.any_form = function
      | Equiv.Local t -> Local (Term.project projs t)
      | Equiv.Global _ as a -> a
    in
    let do_t_proj = Term.project projs in

    { args   = pt.args;
      mv     = Match.Mvar.map do_t_proj pt.mv; 
      system = SE.project_set projs pt.system ;
      subgs  = List.map do_proj pt.subgs;
      form   = do_proj pt.form; }

  let pp fmt (pt : t) : unit =
    Fmt.pf fmt "@[<v 0>\
                @[%a@]@;\
                system : @[%a@]@]"
      Equiv.Any.pp pt.form
      SE.pp_context pt.system
end

(*------------------------------------------------------------------*)
let kind : Equiv.any_form -> [`Global | `Local] = function
  | Local  _ -> `Local
  | Global _ -> `Global

(*------------------------------------------------------------------*)
let is_local : Equiv.any_form -> bool = function
  | Local  _ -> true
  | Global _ -> false

(*------------------------------------------------------------------*)
(* let is_global : Equiv.any_form -> bool = function
 *   | Local  _ -> true
 *   | Global _ -> false *)

(*------------------------------------------------------------------*)
(** Try to localize [pt_f] *)
let pt_try_localize ~(failed : unit -> PT.t) (pt_f : PT.t) : PT.t =
  let rec doit (pt_f : PT.t) : PT.t =
    match pt_f.form with
    | Local _ -> assert false
    | Global (Atom (Reach f)) -> { pt_f with form = Local f; }

    (* [pf_t] is a [forall vs, f]: add [vs] as variables *)
    | Global (Equiv.Quant (Equiv.ForAll, vs, f)) ->
      (* refresh variables *)
      let vs, subst = Term.refresh_vars `Global vs in
      let f = Equiv.subst subst f in

      doit { pt_f with
             args = Sv.add_list pt_f.args vs;
             form = Global f; }

    (* [pf_t] is an implication [f1 -> f2]: add [f1] as hypothesis *)
    | Global (Equiv.Impl (f1, f2)) ->
      doit { pt_f with
             subgs = (Global f1) :: pt_f.subgs;
             form = Global f2; }

    | Global _f -> failed ()

  in
  doit pt_f

(*------------------------------------------------------------------*)
(** Try to localize [pt_f] *)
let pt_try_globalize ~(failed : unit -> 'a) (pt_f : PT.t) : PT.t =
  assert (is_local pt_f.form);

  match pt_f.form with
  | Global _ -> assert false
  | Local f ->
    (* we fail if [pt_f] as any local hypothesis (indeed, a local sequent can 
       be recast as a global sequent only when it has no local hypothesis). *)
    if List.exists is_local pt_f.subgs then failed ()
    else 
      { pt_f with form = Global (Atom (Reach f)); }

(*------------------------------------------------------------------*)
(** Try to cast [pt_f] as a [kind] proof-term conclusion. 
    Raise [failed] in case of failure. *)
let pt_try_cast (type a)
    ~(failed : unit -> 'b)
    (kind : a Equiv.f_kind) (pt : PT.t) : PT.t
  =
  match kind, pt.form with
  | Equiv.Local_t , Local  _ -> pt
  | Equiv.Global_t, Global _ -> pt

  | Equiv.Local_t , Global _ -> pt_try_localize  ~failed pt
  | Equiv.Global_t, Local  _ -> pt_try_globalize ~failed pt

  | Equiv.Any_t, _ -> pt

(** Same as [pt_try_cast], but without GADTs. *)
let pt_try_cast0
    ~(failed : unit -> 'b)
    (kind : [`Local | `Global]) (pt : PT.t) : PT.t
  =
  match kind, pt.form with
  | `Local , Local  _ -> pt
  | `Global, Global _ -> pt

  | `Local , Global _ -> pt_try_localize  ~failed pt
  | `Global, Local  _ -> pt_try_globalize ~failed pt
(*------------------------------------------------------------------*)
(** Projects [pt] onto [system], projecting diffs in terms if necessary.
    Projection must be possible. *)
let pt_project_system_set (pt : PT.t) (system : SE.context) : PT.t =
  (* project local hyps. and conclusion [arg] over [system]. *)
  if SE.is_fset system.set then
    if SE.is_fset pt.system.set then

      (* Use [system] projections in [pt], by renaming [pt]'s projections to 
         projections in [system] for the same single systems. *)
      let _, proj_subst =
        SE.mk_proj_subst ~strict:true ~src:pt.system.set ~dst:system.set 
      in
      let psubst = Equiv.Babel.subst_projs Equiv.Any_t proj_subst in
      let pt = 
        { pt with subgs = List.map psubst pt.subgs;
                  form  = psubst pt.form;
                  system = { pt.system with set = system.set };
                  (* we already set [pt.system] to [system.set], even though 
                     we did not project the diffs yet. *) 
        } 
      in

      (* [system] and [pt.system] are fsets. 
         Project [pt] over [system.set]. *)
      let projs = List.map fst (SE.to_list @@ SE.to_fset system.set) in
      PT.projs_set_in_local projs pt

    (* [system.set] is a fset, [pt.system.set] is [SE.any]
       or [SE.any_compatible_with].
       In that case, no projection needed in terms: simply uses 
       [system.set]. *)
    else { pt with system }
  else
    (* [system.set] is [SE.any] or [SE.any_compatible_with].
       [pt.system.set] must be in the same case. *)
    let () = assert (SE.is_any_or_any_comp pt.system.set) in
    { pt with system }

(*------------------------------------------------------------------*)
(** Check if [pt] is general enough for [system]. 
    Note that we do not use this function in [pt_unify_systems], 
    because it must do more complicated checks. *)
let pt_compatible_with table (pt : PT.t) (system : SE.context) : bool =
  (* Check equivalence systems in [system.pair]. *)
  let comp_pair =
    (* if [pt] has only local subgoals, it is compatible. *)
    ( is_local pt.form && (List.for_all is_local pt.subgs) ) ||

    (* if the target system has no system pair, it is compatible. *)
    system.pair = None ||

    (* or if both system pair are identical *)
    oequal (SE.equal table) system.pair pt.system.pair
  in
  let comp_set =
    SE.subset table system.set pt.system.set
  in
  comp_pair && comp_set 

(*------------------------------------------------------------------*)
let pt_unify_warning ~(pt : PT.t) ~(arg : PT.t) : unit =
  Printer.prt `Warning
    "Proof-term argument@;  @[%a@]@;\
     has less general systems than the proof-term it is applied into@;  @[%a@]@;\
     The latter proof-term's system set has been projected."
    PT.pp arg
    PT.pp pt

(** Unify the systems of [pt] and [arg], prioritizing [pt]'s systems,
    projecting if necessary.
    Raise [failed] in case of failure. *)
let pt_unify_systems
    ~(failed : unit -> 'a)
    (table : Symbols.table)
    ~(pt : PT.t) ~(arg : PT.t)
  : PT.t * PT.t
  =
  (* Check equivalence systems in [system.pair].
     Fails if not compatible. *)
  let arg_pair, pt_pair = arg.system.pair, pt.system.pair in
  if pt_pair <> None && not (oequal (SE.equal table) pt_pair arg_pair) then
    failed ()
  else

    (* Unify reachability systems in [system.set]. *)
    let pt_set, arg_set = pt.system.set, arg.system.set in
    if SE.subset table pt_set arg_set then
      pt, pt_project_system_set arg pt.system 
    else
    if SE.subset table arg_set pt_set then begin
      pt_unify_warning ~pt ~arg;
      pt_project_system_set pt arg.system, arg
    end
    else failed ()


(*------------------------------------------------------------------*)
(** {2 Module type for sequents -- after Prover} *)

type ghyp = [ `Hyp of Ident.t | `Lemma of string ]

module type S = sig
  include LowSequent.S

  (*------------------------------------------------------------------*)
  module Reduce : Reduction.S with type t := t

  (*------------------------------------------------------------------*)
  val is_assumption       : lsymb -> t -> bool
  val is_equiv_assumption : lsymb -> t -> bool
  val is_reach_assumption : lsymb -> t -> bool

  (*------------------------------------------------------------------*)
  val to_general_sequent : t -> Goal.t

  val to_global_sequent : t -> LowEquivSequent.t
                                 
  (*------------------------------------------------------------------*)
  val convert_pt_gen :
    check_compatibility:bool ->
    ?close_pats:bool ->
    Theory.p_pt -> 
    t ->
    ghyp * Type.tvars * PT.t

  val convert_pt :
    ?close_pats:bool ->
    Theory.p_pt -> 
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
  let to_global_sequent = Args.to_global_sequent

  (*------------------------------------------------------------------*)
  let is_assumption (name : lsymb) (s : S.t) =
    Hyps.mem_name (L.unloc name) s ||
    Lemma.mem name (S.table s)

  let is_equiv_assumption (name : lsymb) (s : sequent) =
    Hyps.mem_name (L.unloc name) s ||
    Lemma.mem_equiv name (S.table s)

  let is_reach_assumption (name : lsymb) (s : sequent) =
    Hyps.mem_name (L.unloc name) s ||
    Lemma.mem_reach name (S.table s)

  (*------------------------------------------------------------------*)
  let is_impl_k (type a) (f_kind : a Equiv.f_kind) (f : a) : bool
    =
    match f_kind with
    | Equiv.Local_t  ->  Term.Smart.is_impl f
    | Equiv.Global_t -> Equiv.Smart.is_impl f
    | Equiv.Any_t ->
      match f with
      | Local f -> Term.Smart.is_impl f |
        Global f -> Equiv.Smart.is_impl f

  let destr_impl_k
      (type a)
      (f_kind : a Equiv.f_kind)
      (f      : a)
    : (a * a) option
    =
    match f_kind with
    | Equiv.Local_t  ->  Term.Smart.destr_impl f
    | Equiv.Global_t -> Equiv.Smart.destr_impl f
    | Equiv.Any_t ->
      match f with
      | Local f ->
        omap
          (fun (v,f) -> Equiv.Local v, Equiv.Local f)
          (Term.Smart.destr_impl f)
          
      | Global f ->
        omap
          (fun (v,f) -> Equiv.Global v, Equiv.Global f)
          (Equiv.Smart.destr_impl f)

  let destr_forall1_k
      (type a)
      (f_kind : a Equiv.f_kind)
      (f      : a)
    : (Vars.var * a) option
    =
    match f_kind with
    | Equiv.Local_t  ->  Term.Smart.destr_forall1 f
    | Equiv.Global_t -> Equiv.Smart.destr_forall1 f
    | Equiv.Any_t ->
      match f with
      | Local f ->
        omap (fun (v,f) -> v, Equiv.Local f) (Term.Smart.destr_forall1 f)
      | Global f ->
        omap (fun (v,f) -> v, Equiv.Global f) (Equiv.Smart.destr_forall1 f)

  let decompose_forall_k
      (type a)
      (f_kind : a Equiv.f_kind)
      (f      : a)
    : Vars.vars * a
    =
    match f_kind with
    | Equiv.Local_t  ->  Term.Smart.decompose_forall f
    | Equiv.Global_t -> Equiv.Smart.decompose_forall f
    | Equiv.Any_t ->
      match f with
      | Local f ->
        let vs,f = Term.Smart.decompose_forall f in vs, Local f
      | Global f ->
        let vs,f = Equiv.Smart.decompose_forall f in vs, Global f
  
  (*------------------------------------------------------------------*)
  (** Return the location of a proof term argument. *)
  let pt_arg_loc (p_arg : Theory.p_pt_arg) : L.t =
    match p_arg with
    | PT_term t -> L.loc t
    | PT_sub pt -> pt.p_pt_loc

  let pt_arg_as_term (p_arg : Theory.p_pt_arg) : Theory.term =
    match p_arg with
    | Theory.PT_term t -> t
    | _ ->
      hard_failure ~loc:(pt_arg_loc p_arg) (Failure "expected a term")

  (** A proof term with type [f1 -> f2] argument is either:
      - another proof term whose type [f'] must match [f1] 
      - an underscore, which generates a subgaol for [f1] *)
  type pt_impl_arg = [`Pt of Theory.p_pt | `Subgoal]

  (** Try to interpret a proof term argument as a proof term. *)
  let pt_arg_as_pt (p_arg : Theory.p_pt_arg) : [`Pt of Theory.p_pt | `Subgoal] =
    match p_arg with
    | Theory.PT_sub pt -> `Pt pt

    (* if we gave a term, re-interpret it as a proof term *)
    | Theory.PT_term ({ pl_desc = Symb head } as t) 
    | Theory.PT_term ({ pl_desc = App ({ pl_desc = Symb head }, _) } as t) ->
      let f, terms = Theory.decompose_app t in
      assert (Theory.equal_i (Theory.Symb head) (L.unloc f));

      let pt = Theory.{
          p_pt_head = head;
          p_pt_args = List.map (fun x -> PT_term x) terms ;
          p_pt_loc  = L.loc t;
        } in 
      `Pt pt

    | Theory.PT_term { pl_desc = Theory.Tpat } -> `Subgoal

    | _ ->
      hard_failure ~loc:(pt_arg_loc p_arg) (Failure "expected a term")

  (*------------------------------------------------------------------*)
  let error_pt_nomatch loc ~(prove : PT.t) ~(target : PT.t) =
    let err_str =
      Fmt.str "@[<v 0>the proof term proves:@;  \
               concl  : @[%a@]@;  \
               system : @[%a@]@;\
               but it must prove:@;  \
               concl  : @[%a@]@;  \
               system : @[%a@]@]"
        Equiv.Any.pp prove.form
        SE.pp_context prove.system
        Equiv.Any.pp target.form
        SE.pp_context target.system
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
      parsed as a term (i.e. a [PT_term]. We resolve it as a [PT_sub] using
      the context. *)
  let rec resolve_pt_arg (s : S.t) (pt_arg : Theory.p_pt_arg) : Theory.p_pt_arg =
    match pt_arg with
    | Theory.PT_sub sub -> PT_sub (resolve_pt s sub)
    | Theory.PT_term t  ->
      match L.unloc t with
      | Theory.App ({ pl_desc = Theory.Symb h}, args) ->
        if S.Hyps.mem_name (L.unloc h) s then
          let p_pt_args =
            List.map (fun a -> resolve_pt_arg s (Theory.PT_term a)) args
          in
          let pt = Theory.{
            p_pt_head = h;
            p_pt_args;
            p_pt_loc = last_loc (L.loc h) args;
          } in
          PT_sub pt
        else pt_arg

      | _ -> pt_arg

  and resolve_pt (s : S.t) (pt : Theory.p_pt) : Theory.p_pt =
    Theory.{ pt with p_pt_args = List.map (resolve_pt_arg s) pt.p_pt_args }

  (*------------------------------------------------------------------*)      
  (** Internal 
      Get a proof-term conclusion by name (from a lemma, axiom or hypothesis). *)
  let pt_of_assumption
      ~(table: Symbols.table)
      (ty_env : Type.Infer.env) 
      (name : lsymb)
      (s    : t)
    : ghyp * PT.t
    =
    if Hyps.mem_name (L.unloc name) s then
      let id, f = Hyps.by_name name s in
      let f : Equiv.any_form =
        match S.hyp_kind with
        | Equiv.Any_t -> f
        | src ->
          Equiv.Babel.convert ~loc:(L.loc name) ~src ~dst:Equiv.Any_t f
      in
      
      `Hyp id,
      { system = S.system s;
        subgs  = [];
        mv     = Mvar.empty;
        args   = Sv.empty;
        form   = f; }

    else if not (Lemma.mem name table) then
      soft_failure ~loc:(L.loc name)
        (Failure ("no proved goal named " ^ L.unloc name))

    else
      let lem = Lemma.find_stmt name (S.table s) in

      (* Open the lemma type variables. *)
      let _, tsubst = Type.Infer.open_tvars ty_env lem.ty_vars in
      let form = Equiv.Babel.tsubst Equiv.Any_t tsubst lem.formula in

      `Lemma lem.Goal.name,
      { system = lem.system;
        mv     = Mvar.empty;
        subgs  = [];
        args   = Sv.empty;
        form; }

  (*------------------------------------------------------------------*)
  (** Apply [pt_f] to [p_arg].
      Pop the first universally quantified variable in [f] and
      instantiate it with [pt_arg]*)
  let pt_apply_var_forall
      (pt_f : PT.t) (pt_arg : Term.term)
    : PT.t
    =
    let f_arg, f = oget (destr_forall1_k Equiv.Any_t pt_f.form) in

    (* refresh the variable *)
    let f_arg, fs = Term.refresh_vars `Global [f_arg] in
    let f = Equiv.Any.subst fs f in
    let f_arg = as_seq1 f_arg in

    let new_p_vs = Sv.filter Vars.is_pat (Term.fv pt_arg) in
    let args = Sv.union new_p_vs pt_f.args in

    let mv = Mvar.add f_arg pt_arg pt_f.mv in
    { subgs = pt_f.subgs; args; mv; form = f; system = pt_f.system }

  (*------------------------------------------------------------------*)
  (** Apply [pt_f] to [p_arg] when [pt_f] is an implication. 
      Pop the first implication [f1] of [pt_f.form], instantiate (my matching) it
      using [pt_impl_arg], and return the updated [pt_f].

      Remark: [pt_arg]'s substitution must be an extention of 
      [pt_f]'s substitution. *)
  let pt_apply_var_impl 
      (* ~(loc : L.t)  *) ~(loc_arg : L.t)
      (ty_env : Type.Infer.env) (s : S.t)
      (pt : PT.t) (arg : PT.t)
    : PT.t
    =
    let table = S.table s in
    let f1, f2 = oget (destr_impl_k Equiv.Any_t pt.form) in

    let pt_apply_error arg () =
      error_pt_nomatch loc_arg ~prove:arg ~target:{ pt with form = f1 }
    in

    (* Specializing [pt.form] by an extention of [pt.mv] is always 
       safe. *)
    let sbst = Mvar.to_subst ~mode:`Unif arg.mv in
    let f1 = Equiv.Any.subst sbst f1 in
    let pat_f1 = Term.{
        pat_vars   = pt.args;
        pat_term   = f1;
        pat_tyvars = [];
      } in

    (* Try to case [arg] to the appripriate kind (local or global), 
       depending on [f1] kind. 
       If the cast fails, we raise a user-level error. *)
    let arg =
      pt_try_cast0 ~failed:(pt_apply_error arg) (kind f1) arg
    in

    (* Verify that the systems of the argument [arg] applies to the systems
       of [pt], projecting it if necessary. *)
    let pt, arg =
      pt_unify_systems  ~failed:(pt_apply_error arg) table ~pt ~arg
    in
    
    (* FIXME: unify [f1] and [arg.form] instead of matching.
       This probably allows not to specialize [f1] above. *)
    let match_res =
      match f1, arg.form with
      | Local f1, Local f_arg ->
        let pat_f1 = { pat_f1 with pat_term = f1 } in
        Match.T.try_match
          ~ty_env ~mv:arg.mv
          table pt.system f_arg pat_f1

      | Global f1, Global f_arg  ->
        let pat_f1 = { pat_f1 with pat_term = f1 } in
        Match.E.try_match
          ~ty_env ~mv:arg.mv
          table pt.system f_arg pat_f1

      | _ -> assert false       (* impossible thanks to [pt_try_cast] *)
    in
    let mv = match match_res with
      | Match.FreeTyv   -> assert false
      | Match.NoMatch _ -> pt_apply_error arg ()
      | Match.Match mv  -> mv
    in

    (* Add to [pt.args] the new variables that must be instantiated in
       the proof term [p_arg]. *)
    let args = Sv.union arg.args pt.args in
    let subgs = arg.subgs @ pt.subgs in

    { subgs; mv; args; form = f2; system = pt.system; }

  (*------------------------------------------------------------------*)
  (** Parse a partially applied lemma or hypothesis as a pattern. *)
  let rec _convert_pt_gen 
      (ty_env : Type.Infer.env)
      (init_mv : Mvar.t)
      (pt : Theory.p_pt)
      (s : S.t) : ghyp * PT.t
    =
    let table = S.table s in

    let lem_name, init_pt_f =
      pt_of_assumption ~table ty_env pt.p_pt_head s 
    in
    assert (init_pt_f.mv = Mvar.empty);
    let init_pt_f = { init_pt_f with mv = init_mv; } in

    let cenv = Theory.{ env = S.env s; cntxt = InGoal; } in

    (** Apply [pt_f] to [p_arg] when [pt_f] is a forall. *)
    let do_var (pt_f : PT.t) (p_arg : Theory.term) : PT.t =
      match destr_forall1_k Equiv.Any_t pt_f.form with
      | None ->
        hard_failure ~loc:(L.loc pt.p_pt_head) (Failure "too many arguments");

      | Some (f_arg, _) ->
        let ty = Vars.ty f_arg in
        let arg, _ = Theory.convert ~ty_env ~pat:true cenv ~ty p_arg in

        pt_apply_var_forall pt_f arg
    in

    (** Apply [pt_f] to [p_arg] when [pt_f] is an implication. *)
    let do_impl
        (pt_f : PT.t) (pt_impl_arg : pt_impl_arg)
      : PT.t
      =
      match destr_impl_k Equiv.Any_t pt_f.form, pt_impl_arg with
      | None, _ ->
        hard_failure ~loc:(L.loc pt.p_pt_head) (Failure "too many arguments")

      | Some (f1, f2), `Subgoal ->
        { system = pt_f.system;
          subgs  = f1 :: pt_f.subgs;
          mv     = pt_f.mv;
          args   = pt_f.args;
          form   = f2; }

      | Some _, `Pt p_arg ->
        let _, pt_arg = _convert_pt_gen ty_env pt_f.mv p_arg s in
        pt_apply_var_impl
          (* ~loc:(L.loc pt.p_pt_head) *) ~loc_arg:p_arg.p_pt_loc
          ty_env s
          pt_f pt_arg
    in

    (* fold through the provided arguments and [f],
       instantiating [f] along the way, 
       and accumulating proof obligations. *)
    let pt_f =
      List.fold_left (fun (pt_f : PT.t) (p_arg : Theory.p_pt_arg) ->
          if is_impl_k Equiv.Any_t pt_f.form then
            do_impl pt_f (pt_arg_as_pt p_arg) 
          else
            do_var pt_f (pt_arg_as_term p_arg) 
        ) init_pt_f pt.p_pt_args
    in

    lem_name, pt_f

  (*------------------------------------------------------------------*)
  (** Closes inferred variables from [pt.args] by [pt.mv]. *)
  let close (pt : PT.t) : PT.t =
    (* clear infered variables from [pat_vars] *)
    let args =
      Sv.filter (fun v -> not (Mvar.mem v pt.mv)) pt.args
    in
    (* instantiate infered variables *)
    let subst = Mvar.to_subst ~mode:`Unif pt.mv in
    let form = Equiv.Any.subst subst pt.form in
    let subgs = List.map (Equiv.Any.subst subst) pt.subgs in

    (* the only remaining variables are pattern holes '_' *)
    assert (Sv.for_all Vars.is_pat args);

    (* renamed remaining pattern variables,
       to avoir having variable named '_' in the rest of the prover. *)
    let subst, args =
        Sv.map_fold (fun subst v ->
          let new_v = Vars.make_fresh (Vars.ty v) "x" in
          Term.ESubst (Term.mk_var v, Term.mk_var new_v) :: subst,
          new_v
          ) [] args
    in
    let form = Equiv.Any.subst subst form in
    let subgs = List.map (Equiv.Any.subst subst) subgs in
    { pt with mv = Mvar.empty; subgs; args; form; }

  (*------------------------------------------------------------------*)
  (** Exported. *)
  let convert_pt_gen
      ~check_compatibility
      ?(close_pats=true)
      (p_pt : Theory.p_pt)
      (s    : S.t)
    : ghyp * Type.tvars * PT.t
    =
    (* resolve (to some extent) parser ambiguities in [s] *)
    let p_pt = resolve_pt s p_pt in

    (* create a fresh unienv and matching env *)
    let ty_env = Type.Infer.mk_env () in
    let mv = Mvar.empty in

    (* convert the proof term *)
    let name, pt = _convert_pt_gen ty_env mv p_pt s in

    let pt =
      if not check_compatibility then
        pt
      else if pt_compatible_with (S.table s) pt (S.system s) then
        pt_project_system_set pt (S.system s)
      else
        Tactics.hard_failure Tactics.NoAssumpSystem
    in
    
    (* close the proof-term by inferring as many pattern variables as possible *)
    let pt = close pt in

    (* pattern variable remaining, and not allowed *)
    if close_pats && not (Sv.is_empty pt.args) then
      Tactics.soft_failure Tactics.CannotInferPats;

    (* close the unienv and generalize remaining univars *)
    let pat_tyvars, tysubst = Type.Infer.gen_and_close ty_env in
    let form = Equiv.Babel.tsubst Equiv.Any_t tysubst pt.form in
    let subgs = List.map (Equiv.Babel.tsubst Equiv.Any_t tysubst) pt.subgs in
    let args = Sv.map (Vars.tsubst tysubst) pt.args in

    (* generalize remaining universal variables in f *)
    (* FIXME: don't generalize in convert_pt_gen *)
    let f_args, form = decompose_forall_k Equiv.Any_t form in
    let f_args, subst = Term.refresh_vars `Global f_args in
    let form = Equiv.Any.subst subst form in
    let args =
      List.fold_left (fun args v -> Sv.add v args) args f_args
    in

    let pt = { pt with form; subgs; args; } in

    name, pat_tyvars, pt

  (*------------------------------------------------------------------*)
  (** Exported. *)
  let convert_pt
      ?close_pats
      (pt :  Theory.p_pt)
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
