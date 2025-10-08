(* Typing trace tactic *)
(* Implements the work published in:
    Secrecy by typing in the computational model,
    Stéphanie Delaune, Clément Herouard, Joseph Lallemand
    CSF 2025 *)
open Squirrelcore
open Term
open Utils

module Args = TacticsArgs
module L = Location
module SE = SystemExpr

module TS = TraceSequent

type sequent = TS.sequent

type lsymb = Typing.lsymb

open LowTactics

(*------------------------------------------------------------------*)
let wrap_fail = TraceLT.wrap_fail
let soft_failure = Tactics.soft_failure
let hard_failure = Tactics.hard_failure


(*------------------------------------------------------------------*)
(** {2 Typing tactic} *)

(** Finds the parameters of the integrity functions used in the hypothesis,
    if any *)
let typing_param
    ~(hyp_loc : L.t)
    (hyp : term)
    (s : TS.sequent)
  : term * term
  =
  (* try to write hyp as u = v *)
  match TS.Reduce.destr_eq s Equiv.Local_t hyp with
  | Some (u, v) -> (u, v)
  | None -> soft_failure ~loc:hyp_loc
      (Tactics.Failure "can only be applied on an hypothesis of the form t1 = t2")

(*------------------------------------------------------------------*)

(** Removes any hypothesis in the sequent that is neither global,
    const, or type Bool *)
let filter_hyps (s : sequent) : sequent =
  let valid_hyp (_, hyp : TS.Hyps.ldecl) =
    match hyp with
    | LDef _ -> true
    | LHyp (Global _) -> true
    | LHyp (Local t) ->
      HighTerm.is_constant (TS.env s) t ||
        SecrecyTyping.is_type (TS.env s) t (SecrecyTyping.boolean) = Ok([])
  in
  TS.Hyps.filter valid_hyp s

(** Creates subgoal sequents with formulas given by the typing procedure *)
let generate_subgoals_consts (s : sequent) (forms :term list) : sequent list =
  List.map (fun form -> TS.set_conclusion form s) forms

(** Creates a subgoal sequent for subterm [output@tau] in [t].
    The goal is [conds => exec@tau] with [conds] the conditions under which
    the subterm [output@tau] appears in [t]. *)
let generate_subgoals_output (s : sequent) (t : term) : sequent list =
  let f (t : term)
      (_ : SE.arbitrary)
      (_ : Vars.vars)
      (conds : Term.term list)
      (_ : Match.Pos.pos)
      (acc : sequent list) =
    match t with 
    | Macro(msymb, _, ts) when msymb.s_symb = Symbols.Classic.out ->
      let hap = mk_macro Macros.Classic.exec [] ts in
      let concl =
        List.fold_left
          (fun concl cond -> mk_impl cond concl)
          hap
          conds
      in
      let subgoal = TS.set_conclusion concl s in
      subgoal :: acc, `Map t
    | _ -> acc, `Continue
  in
  let sequents, _, _ = Match.Pos.map_fold f (TS.system s).set [] t in
  sequents

(** Creates a subgoal sequent for subterm [s@tau] in [t].
    The goal is [conds => happens(tau)] with [conds] the conditions under which
    the subterm [output@tau] appears in [t]. *)
let generate_subgoals_states (s : sequent) (t : term) : sequent list =
  let f (t : term)
      (_ : SE.arbitrary)
      (_ : Vars.vars)
      (conds : Term.term list)
      (_ : Match.Pos.pos)
      (acc : sequent list) =
    match t with 
    | Macro(msymb, _, ts) -> begin
      match Symbols.get_macro_data msymb.s_symb (TS.table s) with
      | State _ ->
        let hap = mk_happens ts in
        let concl =
          List.fold_left
            (fun concl cond -> mk_impl cond concl)
            hap
            conds
        in
        let subgoal = TS.set_conclusion concl s in
        subgoal :: acc, `Map t
      | _ -> acc, `Continue
      end
    | _ -> acc, `Continue
  in
  let sequents, _, _ = Match.Pos.map_fold f (TS.system s).set [] t in
  sequents

(*------------------------------------------------------------------*)

(** Raise a failure if [system] is not registered well-typed in [table]. *)
let check_projection table (system : System.Single.t) =
  let well_typed =
    System.well_typed_projection table system.system system.projection
  in
  if not well_typed then
    soft_failure
      (Tactics.Failure "The system is not well-typed.")

(** Try to type the term [t1] Low, and [t2] High.
    If its succeed, it return [Ok(l)] with [l] a list of subgoal sequents.
    Else, it returns [Error(t, sty, e)] with [e] the error obtained while
    trying to type [t] with [sty]. *)
let check_terms s t1 t2 =
  match SecrecyTyping.is_type (TS.env s) t1 (SecrecyTyping.low) with
  | Error e1 ->
    Error(t1, SecrecyTyping.low, e1)
  | Ok (forms1) -> begin
    match SecrecyTyping.is_type (TS.env s) t2 (SecrecyTyping.high) with
    | Error e2 ->
      Error(t2, SecrecyTyping.high, e2)
    | Ok (forms2) ->
      let l = (generate_subgoals_consts s (forms1 @ forms2)) @
        (generate_subgoals_output s (t1)) @
        (generate_subgoals_states s (t1)) @
        (generate_subgoals_output s (t2)) @
        (generate_subgoals_states s (t2)) in
      Ok (l)
    end

(** Apply the tactic to the hypothesis named [h] in the sequent [s].
    Returns a list of subgoal sequents. *)
let typing (h : lsymb) (s : sequent) : sequent list =
  (* Check that typing is enabled *)
  if not (TConfig.security_types (TS.table s)) then
    soft_failure 
      (Tactics.Failure "`typing` must enabled with the flag [securityTypes = true].");
  (* checks that [h] denotes an hypothesis [h: t1 = t2]. *)  
  let _, hyp = TS.Hyps.by_name_k h Hyp s in
  let hyp = as_local ~loc:(L.loc h) hyp in (* FIXME: allow global hyps? *)
  let t1, t2 = typing_param ~hyp_loc:(L.loc h) hyp s in
  (*Removes from the initial sequent any hypothesis that is neither
    global, const, or well-typed*)
  let s = filter_hyps s in
  (*Check that the tactic is used on an finite set of well-typed system*)
  let env = TS.env s in
  if not (SE.is_fset env.system.set) then
    soft_failure 
      (Tactics.Failure "Expected a finite system set expression.");
  let fset = SE.to_fset env.system.set in
  let systems = SE.to_list fset in
  List.iter (fun system -> check_projection env.table (snd system)) systems;

  let check_type acc (proj, single_sys) =
    (*We project the sequent [s] on a single system*)
    let system =
      { env.system with set = SE.(to_arbitrary @@ singleton single_sys) }
    in
    let s = TS.set_conclusion_in_context system (TS.conclusion s) s in
    (*We project the terms [t1] and [t2]*)
    let t1 = Term.project1 proj t1 in
    let t2 = Term.project1 proj t2 in
    (*Try to type t1 with Low and t2 with High*)
    match check_terms s t1 t2 with
    | Ok(seqs) -> acc @ seqs
    | Error(t, sty, e) -> begin
      (*Try to type t1 with High and t2 with Low*)
      match check_terms s t2 t1 with
      | Ok(seqs) -> acc @ seqs
      | Error(t', sty', e') ->
        Printer.pr "Trying to type terms in the equality as High and Low (or vice-versa).@.@.";
        Printer.pr "Typing %a %a:@.%a@."
          Term.pp t
          SecrecyTyping.pp sty
          SecrecyTyping.pp_error e;
        Printer.pr "Typing %a %a:@.%a@."
          Term.pp t'
          SecrecyTyping.pp sty'
          SecrecyTyping.pp_error e';
        soft_failure ~loc:(L.loc h)
          (Tactics.Failure "Term in the equality cannot be typed correctly.")
    end
  in
  List.fold_left check_type [] systems

(*------------------------------------------------------------------*)
let typing_tac args s =
  let hyp = match args with
    | [hyp] -> hyp
    | _ -> 
      hard_failure
        (Failure "typing requires one argument: hypothesis")
  in
  match TraceLT.convert_args s [hyp] (Args.Sort Args.String) with
  | Args.Arg (Args.String hyp) -> wrap_fail (typing hyp) s
  | _ -> bad_args ()

(*------------------------------------------------------------------*)
let () =
  T.register_general "typing"
    ~pq_sound:false
    (LowTactics.gentac_of_ttac_arg typing_tac)
