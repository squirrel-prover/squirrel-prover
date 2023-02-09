module L = Location

module SE = SystemExpr

module TraceHyps = Hyps.TraceHyps

(*------------------------------------------------------------------*)
module type S = sig

  type t
  type sequent = t
  type sequents = sequent list

  val pp     :             Format.formatter -> t -> unit
  val _pp    : dbg:bool -> Format.formatter -> t -> unit
  val pp_dbg :             Format.formatter -> t -> unit

  (*------------------------------------------------------------------*)
  type hyp_form

  type conc_form

  val hyp_kind : hyp_form Equiv.f_kind
  val conc_kind : conc_form Equiv.f_kind

  (*------------------------------------------------------------------*)
  (** default variable information of the sequent *)
  val var_info : Vars.Tag.t

  (*------------------------------------------------------------------*)
  module Hyps : Hyps.S1 with type hyp = hyp_form and type hyps := t

  (** {2 Access to sequent components} *)

  val env : t -> Env.t
  val set_env : Env.t -> t -> t

  val vars : t -> Vars.env
  val set_vars : Vars.env -> t -> t

  val goal : t -> conc_form
  val set_goal : conc_form -> t -> t

  val system : t -> SystemExpr.context

  val set_goal_in_context :
    ?update_local:(Term.term -> Term.term option) ->
    SystemExpr.context -> conc_form -> t -> t

  val table : t -> Symbols.table
  val set_table : Symbols.table -> t -> t

  val ty_vars : t -> Type.tvars

  (*------------------------------------------------------------------*) 
  (** {2 Manipulation of bi-frame elements}
    *
    * These functionalities only make sense for equivalence sequents. *)

  val mem_felem    : int -> t -> bool
  val change_felem : ?loc:L.t -> int -> Term.term list -> t -> t
  val get_felem    : ?loc:L.t -> int -> t -> Term.term

  (*------------------------------------------------------------------*) 
  (** {2 Automated reasoning} *)

  val query_happens : precise:bool -> t -> Term.term -> bool

  val mk_trace_cntxt : ?se:SE.fset -> t -> Constr.trace_cntxt

  val get_trace_hyps : t -> TraceHyps.hyps

  val get_models : t -> Constr.models

  (*------------------------------------------------------------------*) 
  (** {2 Substitution} *)

  val subst : Term.subst -> t -> t

  val rename : Vars.var -> Vars.var -> t -> t

  (*------------------------------------------------------------------*) 
  (** {2 Free variables} *)

  val fv : t -> Vars.Sv.t

  (*------------------------------------------------------------------*) 
  (** {2 Misc} *)

  val map : Equiv.Babel.mapper -> t -> t

  module Hyp : SmartFO.S with type form = hyp_form

  module Conc : SmartFO.S with type form = conc_form
end

(*------------------------------------------------------------------*) 
(** {2 Common utilities for sequent implementations} *)

let setup_set_goal_in_context ~old_context ~new_context ~table ~vars =

  assert (SE.compatible table new_context.SE.set old_context.SE.set);
  assert (match new_context.SE.pair with
            | Some p -> SE.compatible table new_context.SE.set p
            | None -> true);
  assert (match old_context.SE.pair with
            | Some p -> SE.compatible table old_context.SE.set p
            | None -> true);

  (* Flags indicating which parts of the context are changed. *)
  let set_unchanged = new_context.SE.set = old_context.SE.set in
  let pair_unchanged = new_context.SE.pair = old_context.SE.pair in

  (* Can we project formulas from the old to the new context? *)
  let set_projections =
    if SE.is_any_or_any_comp old_context.set then Some (fun f -> f) else
      if SE.subset table new_context.set old_context.set then
        match SE.(to_projs (to_fset new_context.set)) with
          | projs -> Some (fun f -> Term.project projs f)
          | exception SE.(Error Expected_fset) -> assert false
      else
        None
  in

  (* A local hypothesis can be kept with a projection from the old to
     the new system, when it exists. *)
  let update_local f =
    Utils.omap (fun project -> project f) set_projections
  in

  let env = Env.init ~table ~vars ~system:{ new_context with pair = None; } () in
  
  (* For global hypotheses:
    - Reachability atoms are handled as local hypotheses.
    - Other global hypotheses can be kept if their meaning is unchanged
      in the new annotation. This is ensured in [can_keep_global]
      by checking the following conditions on atoms:
      + Reachability atoms are unconstrained if the set annotation
        has not changed. Otherwise they must be pure trace formulas.
      + Equivalence atoms are only allowed if the trace annotation has
        not changed. *)
  let rec can_keep_global = function
    | Equiv.Quant (_,_,f) :: l ->
        can_keep_global (f::l)

    | Impl (f,g) :: l | Equiv.And (f,g) :: l | Or (f,g) :: l ->
        can_keep_global (f::g::l)

    | Atom (Equiv _) :: l -> pair_unchanged && can_keep_global l

    | Atom (Reach a) :: l ->
      ( ( HighTerm.is_constant `Exact env a &&
          HighTerm.is_system_indep env a )
        || set_unchanged )
      && can_keep_global l
        
    | [] -> true
  in
  let update_global f =
    if can_keep_global [f] then Some f else
      match f with
        | Equiv.Atom (Reach f) ->
            Utils.omap (fun f -> Equiv.Atom (Reach f)) (update_local f)
        | _ -> None
  in

  update_local, update_global
