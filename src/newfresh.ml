(** Tactics exploiting a name's freshness. *)

open Term

module NO = NameOccs

module TS = TraceSequent

module Hyps = TS.LocalHyps

module MP = Match.Pos
module Sp = Match.Pos.Sp

open LowTactics

(*------------------------------------------------------------------*)
let wrap_fail = TraceLT.wrap_fail
let soft_failure = Tactics.soft_failure
(* let hard_failure = Tactics.hard_failure *)

type lsymb = Theory.lsymb

type sequent = TS.sequent


(*------------------------------------------------------------------*)
(** Computes parameters for the fresh trace tactic:
    returns n, t such that hyp is n = t or t = n
    (looks under macros if possible *)
let fresh_param
      ~(hyp_loc : L.t) 
      (info : NO.expand_info) 
      (hyp : term)
      (table : Symbols.table)
    : nsymb * term
  =
  let m1, m2 = match NO.destr_eq_expand info hyp with
    | Some (u, v) -> (u,v)
    | None -> soft_failure ~loc:hyp_loc
                (Tactics.Failure "can only be applied on an equality hypothesis")
  in
  let em1 = NO.expand_macro_check_all info m1 in
  let em2 = NO.expand_macro_check_all info m2 in
  let n, t = match em1, em2 with
    | Name ns, _ -> (ns, em2)
    | _, Name ns -> (ns, em1)
    | _ ->
       soft_failure ~loc:hyp_loc
         (Tactics.Failure "can only be applied on an hypothesis of the form t=n or n=t")
  in
  let ty = n.s_typ in
  if not Symbols.(check_bty_info table ty Ty_large) then
    Tactics.soft_failure
      (Failure "the type of this term is not [large]");
  (n, t)


(** A NameOccs.f_fold_occs function, for use with NO.occurrence_goals.
    Looks for occurrences of n in t (ground):
     - if t is n: returns the occurrence
     - otherwise: asks to be called recursively on subterms *)
let get_bad_occs
      (n:nsymb) 
      (retry_on_subterms : unit -> NO.name_occs)
      (rec_call_on_subterms : fv:Vars.vars -> cond:terms -> p:MP.pos -> se:SE.arbitrary -> st:term -> term -> NO.name_occs)
      ~(se:SE.arbitrary)
      ~(info:NO.expand_info)
      ~(fv:Vars.vars)
      ~(cond:terms)
      ~(p:MP.pos)
      ~(st:term)
      (t:term) 
    : NO.name_occs =
  (* handles a few cases, using rec_call_on_subterm for rec calls,
     and calls retry_on_subterm for the rest *)
  match t with
  | Var v when not (Type.is_finite (Vars.ty v)) ->
     raise NO.Var_found
    
  | Name nn when nn.s_symb = n.s_symb ->
     let oinfo = NO.mk_oinfo n st ~ac:(NO.get_action info) in
     [NO.mk_nocc nn oinfo fv cond Sp.empty]
 
  | _ -> retry_on_subterms ()
       


(** Applies fresh to the sequent s and hypothesis m:
    calls fresh_param and then NO.occurrence_goals with get_bad_occs,
    returns the list of produced subgoals *)
let fresh (m : lsymb) (s : sequent) : sequent list =
  let id, hyp = Hyps.by_name m s in
  try
    let contx = TS.mk_trace_cntxt s in
    let table = TS.table s in
    let (n, t) =
      fresh_param ~hyp_loc:(L.loc m) (NO.EI_direct (s, contx)) hyp table
    in
    
    let pp_n ppf () = Fmt.pf ppf "%a" Term.pp_nsymb n
    in
    let get_bad = get_bad_occs n in
    
    NO.occurrence_goals ~pp_ns:(Some pp_n) get_bad s t
  with
  | NO.Var_found ->
     soft_failure
       (Tactics.Failure "can only be applied on ground terms")
  | SE.(Error Expected_fset) ->
     soft_failure Underspecified_system
    

(** fresh trace tactic *)
let fresh_tac args s =
  match TraceLT.convert_args s args (Args.Sort Args.String) with
  | Args.Arg (Args.String str) -> wrap_fail (fresh str) s
  | _ -> bad_args ()

