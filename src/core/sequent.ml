open Utils

module L = Location
module SE = SystemExpr
module LS = LowSequent

module Sv = Vars.Sv
module Mvar = Match.Mvar

module HTerm = HighTerm
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
    args   : (Vars.var * Vars.Tag.t) list;
    (** in reversed order w.r.t. introduction *)
    
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
      (* TODO: system: there is an issue here:
         global hypotheses cannot be left unchanged, but cannot always
         be projected (see comment above)... *)
    in
    let do_t_proj = Term.project projs in

    { args   = pt.args;
      mv     = Match.Mvar.map do_t_proj pt.mv; 
      system = SE.project_set projs pt.system ;
      subgs  = List.map do_proj pt.subgs;
      form   = do_proj pt.form; }

  let _pp ~dbg fmt (pt : t) : unit =
    let pp_subgoals_and_mv fmt =
      if not dbg then () 
      else 
        Fmt.pf fmt "@[<v 2>subgoals:@ @[%a@]@]@;\
                    @[<v 2>mv:@ @[%a@]@]@;"
          (Fmt.list (Equiv.Any._pp ~dbg ?context:None))
          pt.subgs
          (Mvar._pp ~dbg) pt.mv
    in        
    Fmt.pf fmt "@[<v 0>\
                @[%a@]@;\
                @[system : @[%a@]@]@;\
                %t\
                @[vars: @[%a@]@]@]"
      (Equiv.Any._pp ~dbg ?context:None) pt.form  
      SE.pp_context pt.system
      pp_subgoals_and_mv
      (Vars._pp_typed_tagged_list ~dbg) (List.rev pt.args) 

  let pp     = _pp ~dbg:false
  let pp_dbg = _pp ~dbg:true
end

(*------------------------------------------------------------------*)
(** Try to localize [pt] *)
let pt_try_localize ~(failed : unit -> PT.t) (pt : PT.t) : PT.t =
  let rec doit (pt : PT.t) : PT.t =
    match pt.form with
    | Local _ -> pt
    | Global (Atom (Reach f)) -> { pt with form = Local f; }

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
             subgs = (Global f1) :: pt.subgs;
             form = Global f2; }

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

  | Equiv.Local_t , Global _ -> pt_try_localize  ~failed pt
  | Equiv.Global_t, Local  _ -> failed ()
  (* Casting [pt.form] as a [Reach form] may be unsound if [pt] has
     (discharged) local subgoals
     (FIXME: we could check it and cast if there are no local subgoals). *)

  | Equiv.Any_t, _ -> pt

(*------------------------------------------------------------------*)
(** Rename projections in [pt] to use [pt_pair]'s projections, if necessary. *)
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
      system; } 


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
      let psubst = Equiv.Babel.subst_projs Equiv.Any_t `Reach proj_subst in
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
    else
      let () = assert (SE.is_any_or_any_comp pt.system.set) in
      { pt with system }
  else
    (* [system.set] is [SE.any] or [SE.any_compatible_with].
       [pt.system.set] must be in the same case. *)
    let () = assert (SE.is_any_or_any_comp    system.set &&
                     SE.is_any_or_any_comp pt.system.set   ) in
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

(** Check if [pt] is general enough for [system]. 
    Note that we do not use this function in [pt_unify_systems], 
    because it must do more complicated checks.
    Result: 
    - [`ContextIndep] if there are no system-context dependent formulas in 
      the proof-term
    - [`Subset] if there may be system-context dependent formulas, but the 
      system context of the proof-term contains the target system context 
    - [`Failed] if everything else failed. *)
let pt_compatible_with
    table (pt : PT.t) (system : SE.context) 
  : [`Subset | `ContextIndepPT | `Failed] 
  =
  if List.for_all is_system_context_indep (pt.form :: pt.subgs) then 
    `ContextIndepPT
  else 
    begin
    (* Check equivalence systems in [system.pair]. *)
    let comp_pair =
      (* if [pt] has no equivalences, it is compatible. *)
      ( List.for_all no_equiv_any (pt.form :: pt.subgs) ) ||

      (* if the target system has no system pair, it is compatible. *)
      system.pair = None ||

      (* or if both system pair are identical *)
      oequal (SE.equal_modulo table) system.pair pt.system.pair
    in
    let comp_set =
      SE.subset_modulo table system.set pt.system.set
    in
    if comp_pair && comp_set then `Subset else `Failed
  end

(*------------------------------------------------------------------*)
let pt_unify_warning_systems ~(pt : PT.t) ~(arg : PT.t) : unit =
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
  if List.for_all is_system_context_indep (arg.form :: arg.subgs) then 
    pt, { arg with system = pt.system; }
  else if List.for_all is_system_context_indep (pt.form :: pt.subgs) then 
    { pt with system = arg.system; }, arg
  else
    begin
      (* Check equivalence systems in [system.pair].
         Fails if not compatible. *)
      let arg_pair, pt_pair = arg.system.pair, pt.system.pair in
      if pt_pair <> None && not (oequal (SE.equal_modulo table) pt_pair arg_pair) then
        failed ()
      else
        (* Unify projections of [system.pair] for [arg] and [pt]. *)
        let arg = pt_rename_system_pair arg pt_pair in

        (* Unify reachability systems in [system.set]. *)
        let pt_set, arg_set = pt.system.set, arg.system.set in
        if SE.subset_modulo table pt_set arg_set then
          pt, pt_project_system_set arg pt.system 
        else
        if SE.subset_modulo table arg_set pt_set then begin
          pt_unify_warning_systems ~pt ~arg;
          pt_project_system_set pt arg.system, arg
        end
        else failed ()
    end

(*------------------------------------------------------------------*)
(** {2 Module type for sequents -- after Prover} *)

type ghyp = [ `Hyp of Ident.t | `Lemma of string ]

module type S = sig
  include LowSequent.S

  (*------------------------------------------------------------------*)
  module Reduce : Reduction.S with type t := t

  (*------------------------------------------------------------------*)
  val is_assumption        : lsymb -> t -> bool
  val is_global_assumption : lsymb -> t -> bool
  val is_local_assumption  : lsymb -> t -> bool

  (*------------------------------------------------------------------*)
  val to_general_sequent : t -> Goal.t

  val to_global_sequent : t -> LowEquivSequent.t
                                 
  (*------------------------------------------------------------------*)
  val convert_pt_gen :
    check_compatibility:bool ->
    ?close_pats:bool ->
    Theory.pt -> 
    t ->
    ghyp * Type.tvars * PT.t

  val convert_pt :
    ?close_pats:bool ->
    Theory.pt -> 
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

  let is_global_assumption (name : lsymb) (s : sequent) =
    Hyps.mem_name (L.unloc name) s ||
    Lemma.mem_global name (S.table s)

  let is_local_assumption (name : lsymb) (s : sequent) =
    Hyps.mem_name (L.unloc name) s ||
    Lemma.mem_local name (S.table s)

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
        omap (fun (v,f) -> v, Equiv.Local f) (HTerm.Smart.destr_forall1_tagged f)
          
      | Global f ->
        omap (fun (v,f) -> v, Equiv.Global f) (Equiv.Smart.destr_forall1_tagged f)
          
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
  let pt_arg_loc (p_arg : Theory.pt_app_arg) : L.t =
    match p_arg with
    | PTA_term  t -> L.loc t
    | PTA_sub  pt -> L.loc pt

  let pt_app_arg_as_term (p_arg : Theory.pt_app_arg) : Theory.term =
    match p_arg with
    | Theory.PTA_term t -> t
    | _ ->
      hard_failure ~loc:(pt_arg_loc p_arg) (Failure "expected a term")

  (** A proof term with type [f1 -> f2] argument is either:
      - another proof term whose type [f'] must match [f1] 
      - an underscore, which generates a subgaol for [f1] *)
  type pt_impl_arg = [`Pt of Theory.pt | `Subgoal]

  (** Try to interpret a proof term argument as a proof term. *)
  let pt_app_arg_as_pt (p_arg : Theory.pt_app_arg) : [`Pt of Theory.pt | `Subgoal] =
    match p_arg with
    | Theory.PTA_sub pt -> `Pt pt

    (* if we gave a term, re-interpret it as a proof term *)
    | Theory.PTA_term ({ pl_desc = Symb head } as t) 
    | Theory.PTA_term ({ pl_desc = App ({ pl_desc = Symb head }, _) } as t) ->
      let f, terms = Theory.decompose_app t in
      assert (Theory.equal_i (Theory.Symb head) (L.unloc f));
      let loc = L.loc t in
      let pt_cnt = 
        Theory.PT_app {
          pta_head = L.mk_loc (L.loc head) (Theory.PT_symb head);
          pta_args = List.map (fun x -> Theory.PTA_term x) terms ;
          pta_loc  = loc;
        } 
      in 
      `Pt (L.mk_loc loc pt_cnt)

    | Theory.PTA_term { pl_desc = Theory.Tpat } -> `Subgoal

    | _ ->
      hard_failure ~loc:(pt_arg_loc p_arg) (Failure "expected a term")

  (*------------------------------------------------------------------*)
  let error_pt_nomatch loc ~(prove : PT.t) ~(target : PT.t) =
    let err_str =
      Fmt.str "@[<v 0>the proof term proves:@;  \
               @[%a@]@;\
               but it must prove:@;  \
               @[%a@]@]"
        PT.pp prove 
        PT.pp target
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
  let rec resolve_pt_arg (s : S.t) (pt_arg : Theory.pt_app_arg) : Theory.pt_app_arg =
    match pt_arg with
    | Theory.PTA_sub sub -> PTA_sub (resolve_pt s sub)
    | Theory.PTA_term t  ->
      match L.unloc t with
      | Theory.App ({ pl_desc = Theory.Symb h}, args) ->
        if S.Hyps.mem_name (L.unloc h) s then
          let pta_args =
            List.map (fun a -> resolve_pt_arg s (Theory.PTA_term a)) args
          in
          let loc = last_loc (L.loc h) args in
          let pt_cnt = 
            Theory.PT_app {
              pta_head = L.mk_loc (L.loc h) (Theory.PT_symb h);
              pta_args;
              pta_loc = loc;
            } 
          in
          PTA_sub (L.mk_loc loc pt_cnt)
        else pt_arg

      | _ -> pt_arg

  and resolve_pt (s : S.t) (pt : Theory.pt) : Theory.pt =
    let loc = L.loc pt in
    match L.unloc pt with
    | PT_symb _ -> pt

    | PT_localize sub_pt -> 
      L.mk_loc loc (Theory.PT_localize (resolve_pt s sub_pt))

    | PT_app app ->
      let app = 
        Theory.{ app with pta_args = List.map (resolve_pt_arg s) app.pta_args } 
      in
      L.mk_loc loc (Theory.PT_app app)

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
      let id, f = Hyps.by_name_k name Hyp s in
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
        args   = [];
        form   = f; }

    else if not (Lemma.mem name table) then
      soft_failure ~loc:(L.loc name)
        (Failure ("no proved goal named " ^ L.unloc name))

    else
      let lem = Lemma.find_stmt name (S.table s) in

      (* Open the lemma type variables. *)
      let _, tsubst = Type.Infer.open_tvars ty_env lem.ty_vars in
      let form = Equiv.Babel.tsubst Equiv.Any_t tsubst lem.formula in

      (* a local lemma or axiom is actually a global reachability formula *)
      let form = 
        match S.conc_kind, form with
        (* we already downgrade it for local sequents *)
        | Equiv.Local_t, _ -> form

        (* in global sequent, we use it as a global formula  *)
        | Equiv.Global_t, Equiv.Local f -> Equiv.Global (Atom (Reach f))
        | Equiv.Global_t, Equiv.Global _ -> form
          
        | Equiv.Any_t, _ -> assert false (* impossible *)
      in

      `Lemma lem.Goal.name,
      { system = lem.system;
        mv     = Mvar.empty;
        subgs  = [];
        args   = [];
        form; }

  (*------------------------------------------------------------------*)
  (** Extend a variable environment with the variables of [pt] *)
  let venv_of_pt (env : Vars.env) (pt : PT.t) : Vars.env =
    Vars.add_vars pt.args env

  (** Extend an environment with the variables of [pt] *)
  let env_of_pt table system (env : Vars.env) (pt : PT.t) : Env.t =
    Env.init ~table ~system ~vars:(venv_of_pt env pt) ()

  (*------------------------------------------------------------------*)
  let error_pt_apply_not_system_indep loc ~(pt : PT.t) ~(arg : Term.t) =
    let err_str =
      Fmt.str "@[<v 0>The term:@;  @[%a@]@;\
               is not system-independent. It cannot be applied to:@;  @[%a@].@]"
        Term.pp arg
        PT.pp pt
    in
    soft_failure ~loc (Failure err_str)

  (*------------------------------------------------------------------*)
  let error_pt_apply_not_adv loc ~(pt : PT.t) ~(arg : Term.t) =
    let err_str =
      Fmt.str "@[<v 0>The term:@;  @[%a@]@;\
               is not computable by the adversary. It cannot be applied to:@;  @[%a@].@]"
        Term.pp arg
        PT.pp pt
    in
    soft_failure ~loc (Failure err_str)

    (*------------------------------------------------------------------*)
  let error_pt_apply_not_constant loc ~(pt : PT.t) ~(arg : Term.t) =
    let err_str =
      Fmt.str "@[<v 0>The term:@;  @[%a@]@;\
               is not constant. It cannot be applied to:@;  @[%a@].@]"
        Term.pp arg
        PT.pp pt
    in
    soft_failure ~loc (Failure err_str)

  (*------------------------------------------------------------------*)
  (** Apply [pt] to [p_arg].
      Pop the first universally quantified variable in [f] and
      instantiate it with [pt_arg]*)
  let pt_apply_var_forall
      ~(arg_loc:L.t) (table : Symbols.table) (env : Vars.env)
      (pt : PT.t) (pt_arg : Term.term)
    : PT.t
    =
    let (f_arg, f_arg_tag), f = oget (destr_forall1_tagged_k Equiv.Any_t pt.form) in

    (* refresh the variable *)
    let f_arg, fs = Term.refresh_vars [f_arg] in
    let f = Equiv.Any.subst fs f in
    let f_arg = as_seq1 f_arg in

    (* collect hole vars in the argument [pt_arg] *)
    let new_p_vs = Sv.filter Vars.is_pat (Term.fv pt_arg) in
    (* hole vars are global if [pt]'s conclusion is a global quant., i.e.
       if [f_arg_kind] is [`Global]. *)
    let args =
      List.rev_append (List.map (fun x -> x, f_arg_tag) (Sv.elements new_p_vs)) pt.args
    in

    (* check system-independence, if applicable *)
    let () =
      let venv = Vars.add_vars args env in
      let env = Env.init ~table ~system:pt.system ~vars:venv () in
      (* check a variable instantiation *)
      if f_arg_tag.system_indep && not (HTerm.is_system_indep env pt_arg) then
        error_pt_apply_not_system_indep arg_loc ~pt ~arg:pt_arg;

      (* check a variable instantiation *)
      if f_arg_tag.adv && not (HTerm.is_ptime_deducible ~si:false env pt_arg) then
        error_pt_apply_not_adv arg_loc ~pt ~arg:pt_arg;

      if f_arg_tag.const && not (HTerm.is_constant env pt_arg) then
        error_pt_apply_not_constant arg_loc ~pt ~arg:pt_arg;
    in

    let mv =
      Mvar.add (f_arg, f_arg_tag) pt.system.set pt_arg pt.mv
    in
    { subgs = pt.subgs; args; mv; form = f; system = pt.system }

  (*------------------------------------------------------------------*)
  let pt_downgrade_warning ~(pt : PT.t) ~(arg : PT.t) : unit =
    Printer.prt `Warning
      "Proof-term argument@;  @[%a@]@;\
       is local, while the proof-term it is applied into is global@;  @[%a@]@;\
       The latter proof-term has been downgraded to a local proof-term."
      PT.pp arg
      PT.pp pt

  (*------------------------------------------------------------------*)
  let error_pt_apply_bad_kind loc ~(pt : PT.t) ~(arg : PT.t) =
    let err_str =
      Fmt.str "@[<v 0>bad kind: the proof term proves:@;  @[%a@]@;\
               it cannot be applied to:@;  @[%a@].@]"
        PT.pp arg
        PT.pp pt
    in
    soft_failure ~loc (Failure err_str)
  
  (*------------------------------------------------------------------*)
  let subst_of_pt ~loc table (vars : Vars.env) (pt : PT.t) : Term.subst = 
    let pt_venv = venv_of_pt vars pt in
    match Mvar.to_subst ~mode:`Unif table pt_venv pt.mv with
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
      (ty_env : Type.Infer.env) (s : S.t)
      (pt : PT.t) (arg : PT.t)
    : PT.t
    =
    let table = S.table s in

    let apply_kind_error () = error_pt_apply_bad_kind loc_arg ~pt ~arg in

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
        pt_downgrade_warning ~pt ~arg;
        down_pt, arg
        
    in

    let f1, f2 =
      let pt_env = env_of_pt (S.table s) (S.system s) (S.vars s) pt in
      oget (destr_impl_k Equiv.Any_t pt_env pt.form)
    in
    (* Specializing [pt.form] by an extention of [pt.mv]. *)
    (* FIXME: correct location? *)
    let sbst = subst_of_pt ~loc:loc_arg table (S.vars s) arg in
    let f1 = Equiv.Any.subst sbst f1 in
    let pat_f1 = Term.{
        pat_op_vars   = pt.args;
        pat_op_term   = f1;
        pat_op_tyvars = [];
      } in

    let pt_apply_error arg () =
      error_pt_nomatch loc_arg ~prove:arg ~target:{ pt with form = f1 }
    in

    (* Verify that the systems of the argument [arg] applies to the systems
       of [pt], projecting it if necessary. *)
    let pt, arg =
      pt_unify_systems ~failed:(pt_apply_error arg) table ~pt ~arg
    in

    let match_res =
      (* variable environment with both [pt] and [arg] variables (with their tags). *)
      let env = Vars.add_vars (arg.args @ pt.args) (S.vars s) in

      match f1, arg.form with
      | Local f1, Local f_arg ->
        let pat_f1 = { pat_f1 with pat_op_term = f1 } in
        Match.T.try_match
          ~ty_env ~mv:arg.mv ~env
          table pt.system f_arg pat_f1

      | Global f1, Global f_arg  ->
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

    { subgs; mv; args; form = f2; system = pt.system; }

  (*------------------------------------------------------------------*)
  let error_pt_cannot_apply loc (pt : PT.t) =
    let err_str =
      Fmt.str "@[<hov 2>too many argument, cannot apply:@;  @[%a@]@]"
        PT.pp pt
    in
    soft_failure ~loc (Failure err_str)

  (*------------------------------------------------------------------*)
  let error_pt_cannot_localize loc (pt : PT.t) () =
    let err_str =
      Fmt.str "@[<v 0>cannot localize the proof term:@;  @[%a@]@;@]"
        PT.pp pt
    in
    soft_failure ~loc (Failure err_str)
      
  (*------------------------------------------------------------------*)
  (** Parse a partially applied lemma or hypothesis as a pattern. *)
  let rec do_convert_pt_gen 
      (ty_env : Type.Infer.env)
      (mv : Mvar.t)
      (p_pt : Theory.pt)
      (s : S.t) : ghyp * PT.t
    =
    match L.unloc p_pt with
    | Theory.PT_symb symb -> do_convert_symb ty_env mv symb s
    | Theory.PT_app pt_app -> do_convert_pt_app ty_env mv pt_app s
    | Theory.PT_localize p_sub_pt -> 
      let ghyp, sub_pt = do_convert_pt_gen ty_env mv p_sub_pt s in
      let pt = 
        pt_try_localize
          ~failed:(error_pt_cannot_localize (L.loc p_sub_pt) sub_pt) 
          sub_pt 
      in
      ghyp, pt

  and do_convert_symb
      (ty_env  : Type.Infer.env)
      (init_mv : Mvar.t)
      (symb    : Theory.lsymb)
      (s       : S.t) 
    : ghyp * PT.t
    =
    let table = S.table s in
    let lem_name, pt = pt_of_assumption ~table ty_env symb s in
    assert (pt.mv = Mvar.empty);
    let pt = { pt with mv = init_mv; } in
    lem_name, pt

  and do_convert_pt_app
      (ty_env : Type.Infer.env)
      (init_mv : Mvar.t)
      (pt_app : Theory.pt_app)
      (s : S.t) : ghyp * PT.t
    =
    let table, env = S.table s, S.vars s in

    let lem_name, init_pt = 
      do_convert_pt_gen ty_env init_mv pt_app.pta_head s 
    in

    let cenv = Theory.{ env = S.env s; cntxt = InGoal; } in

    (** Apply [pt] to [p_arg] when [pt] is a forall. *)
    let do_var (pt : PT.t) (p_arg : Theory.term) : PT.t =
      match destr_forall1_tagged_k Equiv.Any_t pt.form with
      | None ->
        error_pt_cannot_apply (L.loc pt_app.pta_head) pt

      | Some ((f_arg, _), _) ->
        let ty = Vars.ty f_arg in
        let arg, _ = Theory.convert ~ty_env ~pat:true cenv ~ty p_arg in

        pt_apply_var_forall ~arg_loc:(L.loc p_arg) table env pt arg
    in

    (** Apply [pt] to [p_arg] when [pt] is an implication. *)
    let do_impl
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
          let subst = subst_of_pt ~loc:pt_app.pta_loc table (S.vars s) pt in
          match destr_impl_k Equiv.Any_t pt_env (Equiv.Any.subst subst pt.form) with
          | Some (f1, f2) -> f1, f2
          | None ->
            error_pt_cannot_apply (L.loc pt_app.pta_head) pt
      in

      match pt_impl_arg with
      | `Subgoal ->             (* discharge the subgoal *)
        { system = pt.system;
          subgs  = f1 :: pt.subgs;
          mv     = pt.mv;
          args   = pt.args;
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
      List.fold_left (fun (pt : PT.t) (p_arg : Theory.pt_app_arg) ->
          if destr_forall1_tagged_k Equiv.Any_t pt.form = None then
            do_impl pt (pt_app_arg_as_pt p_arg) 
          else
            do_var pt (pt_app_arg_as_term p_arg) 
        ) init_pt pt_app.pta_args
    in

    lem_name, pt

  (*------------------------------------------------------------------*)
  (** Closes inferred variables from [pt.args] by [pt.mv]. *)
  let close loc (table : Symbols.table) (env : Vars.env) (pt : PT.t) : PT.t =
    (* clear infered variables from [pat_vars] *)
    let args =
      List.filter (fun (v, _) -> not (Mvar.mem v pt.mv)) pt.args
    in
    (* instantiate infered variables *)
    let subst = subst_of_pt ~loc table env pt in 
    let form = Equiv.Any.subst subst pt.form in
    let subgs = List.map (Equiv.Any.subst subst) pt.subgs in

    (* the only remaining variables are pattern holes '_' *)
    assert (List.for_all (fst_map Vars.is_pat) args);

    (* renamed remaining pattern variables,
       to avoir having variable named '_' in the rest of the prover. *)
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
  let error_pt_bad_system loc (pt : PT.t) =
    let err_str =
      Fmt.str "@[<v 0>the proof term proves:@;  @[%a@]@;\
               it does not apply to the current system.@]"
        PT.pp pt
    in
    soft_failure ~loc (NoAssumpSystem err_str)

  (*------------------------------------------------------------------*)
  (** Exported. *)
  let convert_pt_gen
      ~check_compatibility
      ?(close_pats=true)
      (p_pt : Theory.pt)
      (s    : S.t)
    : ghyp * Type.tvars * PT.t
    =
    (* resolve (to some extent) parser ambiguities in [s] *)
    let p_pt = resolve_pt s p_pt in
    let loc = L.loc p_pt in

    (* create a fresh unienv and matching env *)
    let ty_env = Type.Infer.mk_env () in
    let mv = Mvar.empty in

    (* convert the proof term *)
    let name, pt = do_convert_pt_gen ty_env mv p_pt s in

    let pt =
      if not check_compatibility then
        pt
      else 
        match pt_compatible_with (S.table s) pt (S.system s) with
        | `Subset         -> pt_project_system_set pt (S.system s)
        | `ContextIndepPT -> { pt with system = S.system s; }
        | `Failed         -> error_pt_bad_system loc pt 
    in

    (* close the proof-term by inferring as many pattern variables as possible *)
    let pt = close loc (S.table s) (S.vars s) pt in
    assert (pt.mv = Mvar.empty);

    (* pattern variable remaining, and not allowed *)
    if close_pats && not (pt.args = []) then
      Tactics.soft_failure Tactics.CannotInferPats;

    (* close the unienv and generalize remaining univars *)
    let pat_tyvars, tysubst = Type.Infer.gen_and_close ty_env in
    let form = Equiv.Babel.tsubst Equiv.Any_t tysubst pt.form in
    let subgs = List.map (Equiv.Babel.tsubst Equiv.Any_t tysubst) pt.subgs in
    let args = List.map (fun (v, info) -> Vars.tsubst tysubst v, info) pt.args in

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
      (pt :  Theory.pt)
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
