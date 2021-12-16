open Utils

module L = Location
module SE = SystemExpr
module LS = LowSequent

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
(** {2 Module type for sequents -- after Prover} *)

type ghyp = [ `Hyp of Ident.t | `Lemma of string ]

module type S = sig
  include LowSequent.S
                 
  val is_assumption       : lsymb -> t -> bool
  val is_equiv_assumption : lsymb -> t -> bool
  val is_reach_assumption : lsymb -> t -> bool

  val to_general_sequent : t -> Goal.t
    
  val get_assumption :
    ?check_compatibility:bool ->
    'a Equiv.f_kind -> Theory.lsymb -> t -> (ghyp, 'a) Goal.abstract_statement

  val reduce : Reduction.red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a

  val convert_pt_gen :
    ?check_compatibility:bool -> 
    Theory.p_pt -> 
    'a Equiv.f_kind -> t -> 
    ghyp * SE.t * 'a Match.pat

  val convert_pt :
    Theory.p_pt ->
    'a Equiv.f_kind -> t -> 
    ghyp * 'a Match.pat
end

(*------------------------------------------------------------------*)
module type MkArgs = sig
  module S : LowSequent.S
  val to_general_sequent : S.t -> Goal.t
end


module Mk (Args : MkArgs) : S with
  type t         = Args.S.t         and
  type conc_form = Args.S.conc_form and
  type hyp_form  = Args.S.hyp_form
= struct
  module S = Args.S
  include S

  let to_general_sequent = Args.to_general_sequent

  let is_assumption (name : lsymb) (s : S.t) =
    Hyps.mem_name (L.unloc name) s || Prover.is_assumption (L.unloc name)

  let is_equiv_assumption (name : lsymb) (s : sequent) =
    Hyps.mem_name (L.unloc name) s || Prover.is_equiv_assumption (L.unloc name)

  let is_reach_assumption (name : lsymb) (s : sequent) =
    Hyps.mem_name (L.unloc name) s || Prover.is_reach_assumption (L.unloc name)

  let get_assumption 
      (type a)
      ?(check_compatibility=true) 
      (k    : a Equiv.f_kind)
      (name : lsymb)
      (s    : t)
    : (ghyp, a) Goal.abstract_statement
    =
    if Hyps.mem_name (L.unloc name) s then
      let id, f = Hyps.by_name name s in
      Goal.{ name = `Hyp id;
             system = system s;
             ty_vars = [];
             formula =
               Equiv.Babel.convert
                 ~loc:(L.loc name)
                 ~src:S.hyp_kind
                 ~dst:k
                 f }
    else
      let lem = Prover.get_assumption name in
      (* Verify that it applies to the current system. *)
      if check_compatibility then begin
        match k with
        | Equiv.Local_t
        | _ when Goal.is_reach_statement lem ->
          if not (SE.systems_compatible (S.system s) lem.system) then
            Tactics.hard_failure Tactics.NoAssumpSystem;
        | _ ->
          if S.system s <> lem.system then
            Tactics.hard_failure Tactics.NoAssumpSystem
      end;
      { Goal.name = `Lemma lem.Goal.name ;
        system = lem.system ;
        ty_vars = lem.ty_vars ;
        formula = 
          Equiv.Babel.convert lem.formula
            ~src:Equiv.Any_t ~dst:k ~loc:(L.loc name) }

  (*------------------------------------------------------------------*)
  let is_impl_k (type a) (f_kind : a Equiv.f_kind) (f : a) : bool
    =
    match f_kind with
    | Equiv.Local_t  ->  Term.Smart.is_impl f
    | Equiv.Global_t -> Equiv.Smart.is_impl f
    | Equiv.Any_t ->
      match f with 
      | `Reach f -> Term.Smart.is_impl f | 
        `Equiv f -> Equiv.Smart.is_impl f

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
      | `Reach f ->
        omap (fun (v,f) -> `Reach v, `Reach f) (Term.Smart.destr_impl f) 
      | `Equiv f ->
        omap (fun (v,f) -> `Equiv v, `Equiv f) (Equiv.Smart.destr_impl f) 

  let destr_forall1_k
      (type a)
      (f_kind : a Equiv.f_kind) 
      (f      : a) 
    : (Vars.evar * a) option
    =
    match f_kind with
    | Equiv.Local_t  ->  Term.Smart.destr_forall1 f
    | Equiv.Global_t -> Equiv.Smart.destr_forall1 f
    | Equiv.Any_t ->
      match f with
      | `Reach f ->
        omap (fun (v,f) -> v, `Reach f) (Term.Smart.destr_forall1 f) 
      | `Equiv f ->
        omap (fun (v,f) -> v, `Equiv f) (Equiv.Smart.destr_forall1 f) 

  let decompose_forall_k
      (type a)
      (f_kind : a Equiv.f_kind) 
      (f      : a) 
    : Vars.evars * a 
    =
    match f_kind with
    | Equiv.Local_t  ->  Term.Smart.decompose_forall f
    | Equiv.Global_t -> Equiv.Smart.decompose_forall f
    | Equiv.Any_t ->
      match f with
      | `Reach f ->
        let vs,f = Term.Smart.decompose_forall f in vs, `Reach f
      | `Equiv f ->
        let vs,f = Equiv.Smart.decompose_forall f in vs, `Equiv f

  (*------------------------------------------------------------------*)
  (** Parse a partially applied lemma or hypothesis as a pattern. *)
  let convert_pt_gen 
      (type a)
      ?(check_compatibility=true) 
      (pt     : Theory.p_pt)
      (f_kind : a Equiv.f_kind) 
      (s      : S.t) 
    : ghyp * SE.t * a Match.pat 
    =
    let lem = get_assumption ~check_compatibility f_kind pt.p_pt_head s in

    (* create a fresh unienv *)
    let ty_env = Type.Infer.mk_env () in
    (* open the lemma type variables *)
    let tvars, tsubst = Type.Infer.open_tvars ty_env lem.ty_vars in
    let f = Equiv.Babel.tsubst f_kind tsubst lem.formula in

    let cenv = Theory.{ table = S.table s; cntxt = InGoal; } in 
    let pat_vars = ref (Vars.Sv.of_list []) in

    (* Pop the first universally quantified variables in [f], 
       instantiate it with [p_arg], and return the updated substitution
       and term. *)
    let do_var (subst, f) (p_arg : Theory.term) : Term.esubst list * a =
      match destr_forall1_k f_kind f with
      | None ->
        hard_failure 
          ~loc:(L.loc pt.p_pt_head)
          (Failure "too many arguments");

      | Some (f_arg, f) ->
        (* refresh the variable *)
        let f_arg, fs = Term.erefresh_vars `Global [f_arg] in
        let f = Equiv.Babel.subst f_kind fs f in
        let Vars.EVar f_arg = as_seq1 f_arg in

        let ty = Vars.ty f_arg in
        let t = 
          Theory.convert 
            ~ty_env ~pat:true
            cenv (S.ty_vars s) (S.env s) 
            p_arg ty
        in
        let new_p_vs = 
          Vars.Sv.filter (fun (Vars.EVar v) -> Vars.is_pat v) (Term.fv t)
        in
        pat_vars := Vars.Sv.union (!pat_vars) new_p_vs;
        let subst = 
          Term.ESubst (Term.mk_var f_arg, t) :: subst
        in
        subst, f
    in

    (* Pop the first implication in [f], 
       instantiate it with [p_arg], and return the updated substitution
       and term. *)
    let do_impl (subst, f) (p_arg : Theory.term) : Term.esubst list * a =
      match destr_impl_k f_kind f with
      | None ->
        hard_failure 
          ~loc:(L.loc pt.p_pt_head)
          (Failure "too many arguments");

      | Some (f1, f) ->
        hard_failure 
          ~loc:(L.loc pt.p_pt_head)
          (Failure "cannot instantiate an implication (yet)");
    in

    (* fold through the provided arguments and [f], 
       instantiating [f] along the way. *)
    let subst, f = 
      List.fold_left (fun (subst, f) (p_arg : Theory.term) ->
          if is_impl_k f_kind f then
            do_impl (subst, f) p_arg
          else
            do_var (subst, f) p_arg
        ) ([], f) pt.p_pt_args
    in
    (* instantiate [f_args0] by [args] *)
    let f = Equiv.Babel.subst f_kind subst f in

    (* generalize remaining universal variables in f *)
    let f_args, f = decompose_forall_k f_kind f in
    let f_args, subst = Term.erefresh_vars `Global f_args in
    let f = Equiv.Babel.subst f_kind subst f in
    List.iter (fun v -> pat_vars := Vars.Sv.add v !pat_vars) f_args;

    (* close the unienv and generalize remaining univars*)
    let pat_tyvars, tysubst = Type.Infer.gen_and_close ty_env in
    let f = Equiv.Babel.tsubst f_kind tysubst f in
    let pat_vars = Vars.Sv.map (Vars.tsubst_e tysubst) !pat_vars in

    let pat = Match.{ 
        pat_tyvars;
        pat_vars;
        pat_term = f; } 
    in      
    lem.name, lem.system, pat


  let convert_pt 
      (type a)
      (pt :  Theory.p_pt)
      (f_kind : a Equiv.f_kind)
      (s : S.t)
    : ghyp * a Match.pat 
    = 
    let name, se, pat = 
      convert_pt_gen ~check_compatibility:true pt f_kind s 
    in
    name, pat


  (*------------------------------------------------------------------*)
  module Reduce = Reduction.Mk(S)

  let reduce = Reduce.reduce 
end
