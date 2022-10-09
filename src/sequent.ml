open Utils

module L = Location
module SE = SystemExpr
module LS = LowSequent

module Sv = Vars.Sv

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

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
    'a Equiv.f_kind -> t ->
    ghyp * SE.context * 'a list * 'a Term.pat

  val convert_pt :
    ?close_pats:bool ->
    Theory.p_pt ->
    'a Equiv.f_kind -> t ->
    ghyp * 'a list * 'a Term.pat
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

  let is_assumption (name : lsymb) (s : S.t) =
    Hyps.mem_name (L.unloc name) s ||
    Lemma.mem name (S.table s)

  let is_equiv_assumption (name : lsymb) (s : sequent) =
    Hyps.mem_name (L.unloc name) s ||
    Lemma.mem_equiv name (S.table s)

  let is_reach_assumption (name : lsymb) (s : sequent) =
    Hyps.mem_name (L.unloc name) s ||
    Lemma.mem_reach name (S.table s)

  (* Get assumption by name.
     If required, check for compatibility, i.e. ensure that the assumption
     can be incorporated into the sequent under its own system annotation
     without changing its meaning (projections are performed if needed).
     TODO the compatibility check does not make sense here,
       and must be handled in convert_pt (which needs to be extensively
       reworked)  *)
  let get_assumption
      (type a)
      ~check_compatibility
      ~(table: Symbols.table)
      (k    : a Equiv.f_kind)
      (name : lsymb)
      (s    : t)
    : (ghyp, a) Goal.abstract_statement
    =
    if Hyps.mem_name (L.unloc name) s then
      let id, f = Hyps.by_name name s in
      let make_goal f =
        Goal.{ name    = `Hyp id;
               system  = S.system s;
               ty_vars = [] ;
               formula = f }
      in
      (* Convert to kind [k] with special case when
         [k = Local_t] and [S.hyp_kind = Any_t] where we
         allow an implicit conversion from global to local
         hypothesis. *)
      match k,S.hyp_kind,f with
      | Equiv.Local_t, Equiv.Any_t, Local f ->
        make_goal f
      | Equiv.Local_t, Equiv.Any_t, Global (Equiv.Atom (Reach f)) ->
        make_goal f
      | dst,src,f ->
        make_goal (Equiv.Babel.convert ~loc:(L.loc name) ~src ~dst f)
          
    else if not (Lemma.mem name (S.table s)) then
      soft_failure ~loc:(L.loc name)
        (Failure ("no proved goal named " ^ L.unloc name))

    else
      let lem = Lemma.find_stmt name (S.table s) in
      (* Verify that it applies to the current system. *)
      if check_compatibility then begin
        match k with
        | Equiv.Local_t

        | _ when Goal.is_reach_statement lem ->
          if not (SE.subset table (S.system s).set lem.system.set) then
            Tactics.hard_failure Tactics.NoAssumpSystem

        | _ ->
          if S.system s <> lem.system then
            Tactics.hard_failure Tactics.NoAssumpSystem
      end;
      let formula =
        if SE.is_fset lem.system.set then
          (* TODO shouldn't we project to the sequent's systems
               it also feels unsafe to do this when check_compatibility=false,
               or to just leave the else branch unguarded *)
          let projs = List.map fst (SE.to_list @@ SE.to_fset lem.system.set) in
          Equiv.Any.project projs lem.formula
        else
          lem.formula
      in

      { Goal.name = `Lemma lem.Goal.name ;
        system  = lem.system ;
        ty_vars = lem.ty_vars ;
        formula =
          Equiv.Babel.convert formula
            ~src:Equiv.Any_t ~dst:k ~loc:(L.loc name) }

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

  let error_pt_nomatch loc f_kind prove target =
    let err_str =
      Fmt.str "@[<v 0>the proof term proves:@;  \
               @[%a@]@;\
               but it must prove:@;  \
               @[%a@]@]"
        (Equiv.Babel.pp f_kind) prove
        (Equiv.Babel.pp f_kind) target
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
  (** Parse a partially applied lemma or hypothesis as a pattern. *)
  let rec _convert_pt_gen : type a.
    check_compatibility:bool ->
    Type.Infer.env ->
    Match.Mvar.t ->
    Theory.p_pt ->
    a Equiv.f_kind ->
    S.t ->
    ghyp * SE.context * a list * a Term.pat * Match.Mvar.t
    = fun ~check_compatibility ty_env mv pt f_kind s ->
      let table = S.table s in
      let lem =
        get_assumption ~check_compatibility ~table f_kind pt.p_pt_head s
      in

      (* Open the lemma type variables. *)
      let tvars, tsubst = Type.Infer.open_tvars ty_env lem.ty_vars in
      let f = Equiv.Babel.tsubst f_kind tsubst lem.formula in

      let cenv = Theory.{ env = S.env s; cntxt = InGoal; } in
      let pat_vars = ref (Sv.of_list []) in

      (* Pop the first universally quantified variable in [f],
         instantiate it with [p_arg], and return the updated substitution
         and term. *)
      let do_var (mv, f) (p_arg : Theory.term) : Match.Mvar.t * a =
        match destr_forall1_k f_kind f with
        | None ->
          hard_failure
            ~loc:(L.loc pt.p_pt_head)
            (Failure "too many arguments");

        | Some (f_arg, f) ->
          (* refresh the variable *)
          let f_arg, fs = Term.refresh_vars `Global [f_arg] in
          let f = Equiv.Babel.subst f_kind fs f in
          let f_arg = as_seq1 f_arg in

          let ty = Vars.ty f_arg in
          let t, _ = Theory.convert ~ty_env ~pat:true cenv ~ty p_arg in

          let new_p_vs = Sv.filter Vars.is_pat (Term.fv t) in
          pat_vars := Sv.union (!pat_vars) new_p_vs;

          let mv = Match.Mvar.add f_arg t mv in
          mv, f
      in

      (* Pop the first implication [f1] of [f], instantiate (my matching) it
         using [p_arg], and return:
         - the subgoals under which the proof-term resulting from [p_arg] holds
         - the updated substitution and term
         - the rhs [f2] of [f] *)
      let do_impl
          (mv, f) (pt_impl_arg : pt_impl_arg) : a list * Match.Mvar.t * a 
        =
        match destr_impl_k f_kind f, pt_impl_arg with
        | None, _ ->
          hard_failure
            ~loc:(L.loc pt.p_pt_head)
            (Failure "too many arguments")

        | Some (f1, f2), `Subgoal -> [f1], mv, f2

        | Some (f1, f2), `Pt p_arg ->
          (* TODO do not ignore the system *)
          let _, _, subgs, pat1, mv =
            _convert_pt_gen ~check_compatibility ty_env mv p_arg f_kind s in
          assert (pat1.pat_tyvars = []);

          let subst = Match.Mvar.to_subst ~mode:`Unif mv in
          let f1 = Equiv.Babel.subst f_kind subst f1 in
          let pat_f1 = Term.{
              pat_vars = !pat_vars;
              pat_term = f1;
              pat_tyvars = [];
            } in

          let match_res = match f_kind with
            | Equiv.Local_t ->
              Match.T.try_match
                ~ty_env ~mv
                (S.table s) (S.system s) pat1.pat_term pat_f1

            | Equiv.Global_t ->
              Match.E.try_match
                ~ty_env ~mv
                (S.table s) (S.system s) pat1.pat_term pat_f1

            | Equiv.Any_t ->
              match f1, pat1.pat_term with
              |  Local f1, Local t1 ->
                let pat1   = { pat1 with pat_term = t1 } in
                let pat_f1 = { pat1 with pat_term = f1 } in
                Match.T.try_match
                  ~ty_env ~mv
                  (S.table s) (S.system s) pat1.pat_term pat_f1

              | Global f1, Global t1  ->
                let pat1   = { pat1 with pat_term = t1 } in
                let pat_f1 = { pat1 with pat_term = f1 } in
                Match.E.try_match
                  ~ty_env ~mv
                  (S.table s) (S.system s) pat1.pat_term pat_f1

              | _ -> (* TODO: improve error message *)
                hard_failure ~loc:(L.loc pt.p_pt_head) (Failure "kind error");
          in
          let mv = match match_res with
            | Match.FreeTyv -> assert false
            | Match.NoMatch _ ->
              error_pt_nomatch p_arg.p_pt_loc f_kind pat1.pat_term f1
            | Match.Match mv -> mv
          in

          (* Add to [pat_vars] the new variables that must be instantiated in
             the proof term [p_arg]. *)
          pat_vars := Sv.union pat1.pat_vars !pat_vars;

          (subgs, mv, f2)
      in

      (* fold through the provided arguments and [f],
         instantiating [f] along the way, 
         and accumulating proof obligations. *)
      let subgs, mv, f =
        List.fold_left (fun (subgs, mv, f) (p_arg : Theory.p_pt_arg) ->
            if is_impl_k f_kind f then
              let subgs', mv, f = do_impl (mv, f) (pt_arg_as_pt p_arg) in
              subgs' @ subgs, mv, f
            else
              let mv, f = do_var (mv, f) (pt_arg_as_term p_arg) in
              subgs, mv, f
          ) ([], mv, f) pt.p_pt_args
      in
      let pat = Term.{
          pat_tyvars = [];
          pat_vars = !pat_vars;
          pat_term = f; }
      in
      lem.name, lem.system, subgs, pat, mv


  let close 
      (type a)
      (mv : Match.Mvar.t)
      (f_kind : a Equiv.f_kind)
      (subgs : a list)
      (pat : a Term.pat)
    : a list * a Term.pat       (* sub-goals, pattern *)
    =
    (* clear infered variables from [pat_vars] *)
    let pat_vars =
      Sv.filter (fun v -> not (Match.Mvar.mem v mv)) pat.pat_vars
    in
    (* instantiate infered variables *)
    let subst = Match.Mvar.to_subst ~mode:`Unif mv in
    let f = Equiv.Babel.subst f_kind subst pat.pat_term in
    let subgs = List.map (Equiv.Babel.subst f_kind subst) subgs in

    assert (Sv.for_all Vars.is_pat pat_vars);

    (* renamed remaining pattern variables,
       to avoir having variable named '_' in the rest of the prover. *)
    let subst, pat_vars =
        Sv.map_fold (fun subst v ->
          let new_v = Vars.make_fresh (Vars.ty v) "x" in
          Term.ESubst (Term.mk_var v, Term.mk_var new_v) :: subst,
          new_v
          ) [] pat_vars
    in
    let f = Equiv.Babel.subst f_kind subst f in
    let subgs = List.map (Equiv.Babel.subst f_kind subst) subgs in
    subgs, { pat with pat_vars; pat_term = f; }

  (** Exported. *)
  let convert_pt_gen
      (type a)
      ~check_compatibility
      ?(close_pats=true)
      (pt     : Theory.p_pt)
      (f_kind : a Equiv.f_kind)
      (s      : S.t)
    : ghyp * SE.context * a list * a Term.pat
    =
    (* resolve (to some extent) parser ambiguities in [s] *)
    let pt = resolve_pt s pt in

    (* create a fresh unienv and matching env *)
    let ty_env = Type.Infer.mk_env () in
    let mv = Match.Mvar.empty in

    (* convert the proof term *)
    let name, system, subgs, pat, mv =
      _convert_pt_gen ~check_compatibility ty_env mv pt f_kind s
    in

    (* close the pattern by inferring as many pattern variables as possible *)
    let subgs, pat = close mv f_kind subgs pat in
    let pat_vars, f = pat.pat_vars, pat.pat_term in

    (* pattern variable remaining, and not allowed *)
    if close_pats && not (Sv.is_empty pat_vars) then
      Tactics.soft_failure Tactics.CannotInferPats;

    (* close the unienv and generalize remaining univars *)
    let pat_tyvars, tysubst = Type.Infer.gen_and_close ty_env in
    let f = Equiv.Babel.tsubst f_kind tysubst f in
    let subgs = List.map (Equiv.Babel.tsubst f_kind tysubst) subgs in
    let pat_vars = Sv.map (Vars.tsubst tysubst) pat_vars in

    (* generalize remaining universal variables in f *)
    (* FIXME: don't generalize in convert_pt_gen *)
    let f_args, f = decompose_forall_k f_kind f in
    let f_args, subst = Term.refresh_vars `Global f_args in
    let f = Equiv.Babel.subst f_kind subst f in
    let pat_vars =
      List.fold_left (fun pat_vars v -> Sv.add v pat_vars) pat_vars f_args
    in

    let pat = Term.{
        pat_tyvars;
        pat_vars;
        pat_term = f; }
    in

    name, system, subgs, pat

  (** Exported. *)
  let convert_pt
      ?close_pats
      (type a)
      (pt :  Theory.p_pt)
      (f_kind : a Equiv.f_kind)
      (s : S.t)
    : ghyp * a list * a Term.pat
    =
    let name, se, subgs, pat =
      convert_pt_gen ~check_compatibility:true ?close_pats pt f_kind s
    in
    name, subgs, pat

  (*------------------------------------------------------------------*)
  module Reduce = Reduction.Mk(S)
end
