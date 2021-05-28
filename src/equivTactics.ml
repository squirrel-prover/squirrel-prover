(** All equivalence tactics.
   Tactics are organized in three classes:
    - Logical -> relies on the logical properties of the sequent.
    - Strucutral -> relies on properties of protocols, or of equality over messages,...
    - Cryptographic -> relies on a cryptographic assumptions, that must be assumed.*)
open Utils

module T = Prover.EquivTactics
module Args = TacticsArgs
module L = Location
module SE = SystemExpr

open LowTactics

module ES = EquivSequent
module TS = TraceSequent

module Hyps = ES.Hyps

type tac = ES.t Tactics.tac

type lsymb = Theory.lsymb
type sequent = ES.sequent

module LT = LowTactics.LowTac(EquivSequent)

(*------------------------------------------------------------------*)
(** {2 Utilities} *)

let split_equiv_goal i s =
  try List.splitat i (ES.goal_as_equiv s) 
  with List.Out_of_range ->
    soft_failure (Tactics.Failure "out of range position")
  

(*------------------------------------------------------------------*)
(* same as [LT.wrap_fail], but for goals *)
let wrap_fail f (s: Goal.t) sk fk =
  try sk (f s) fk with
  | Tactics.Tactic_soft_failure e -> fk e

(*------------------------------------------------------------------*)
(** {2 Logical Tactics} *)

(** Wrap a tactic expecting an equivalence goal (and returning arbitrary
  * goals) into a tactic expecting a general prover goal (which fails
  * when that goal is not an equivalence). *)
let only_equiv t (s : Goal.t) =
  match s with
  | Goal.Equiv s -> t s
  | _ -> soft_failure (Tactics.Failure "equivalence goal expected")

(** As [only_equiv], but with an extra arguments. *)
let only_equiv_arg t arg (s : Goal.t) =
  match s with
  | Goal.Equiv s -> t arg s
  | _ -> soft_failure (Tactics.Failure "equivalence goal expected")

(** Wrap a tactic expecting and returning equivalence goals
  * into a general prover tactic. *)
let pure_equiv t s sk fk =
  let t' s sk fk =
    t s (fun l fk -> sk (List.map (fun s -> Goal.Equiv s) l) fk) fk
  in
  only_equiv t' s sk fk

(** As [pure_equiv], but with an extra arguments. *)
let pure_equiv_arg t a s sk fk =
  let t' s sk fk =
    t a s (fun l fk -> sk (List.map (fun s -> Goal.Equiv s) l) fk) fk
  in
  only_equiv t' s sk fk


(** Wrap a functiin expecting an equivalence goal (and returning arbitrary
  * goals) into a tactic expecting a general prover goal (which fails
  * when that goal is not an equivalence). *)
let only_equiv_typed t arg (s : Goal.t) =
  match s with
  | Goal.Equiv s -> t arg s
  | _ -> soft_failure (Tactics.Failure "equivalence goal expected")

(** Wrap a function expecting an argument and an equivalence goal and returning
   equivalence goals into a general prover function. *)
let pure_equiv_typed t arg s =
  let res = only_equiv_typed t arg s in
 List.map (fun s -> Goal.Equiv s) res


(*------------------------------------------------------------------*)
(** Build the sequent showing that a timestamp happens. *)
let happens_premise (s : ES.t) (a : Term.timestamp) =
  let s = ES.trace_seq_of_equiv_seq ~goal:(Term.Atom (`Happens a)) s in
  Goal.Trace s

(*------------------------------------------------------------------*)
(** Admit tactic *)
let () =
  T.register_general "admit"
    ~tactic_help:{general_help = "Admit the current goal, or admit an element \
                                  from a  bi-frame.";
                  detailed_help = "This tactic, of course, is not sound";
                  usages_sorts = [Sort Args.Int];
                  tactic_group = Logical}
    (function
       | [] -> only_equiv (fun _ sk fk -> sk [] fk)
       | [Args.Int_parsed i] ->
           pure_equiv begin fun s sk fk ->
             sk [ES.change_felem i [] s] fk
           end
       | _ -> bad_args ())


(*------------------------------------------------------------------*)
exception NoReflMacros

class exist_macros ~(cntxt:Constr.trace_cntxt) = object (self)
  inherit Iter.iter ~cntxt as super
  method visit_message t = match t with
    | Term.Macro _ -> raise NoReflMacros
    | _ -> super#visit_message t
end


(** Tactic that succeeds (with no new subgoal) on equivalences
  * where the two frames are identical. *)
let refl (e : Equiv.equiv) (s : ES.t) =
  let iter =
    new exist_macros ~cntxt:(ES.mk_trace_cntxt s) in
  try
    (* we check that the frame does not contain macro *)
    List.iter iter#visit_message e;
    if ES.get_frame PLeft s = ES.get_frame PRight s
    then `True
    else `NoRefl
  with
  | NoReflMacros -> `NoReflMacros


(** Tactic that succeeds (with no new subgoal) on equivalences
  * where the two frames are identical. *)
let refl_tac (s : ES.t) =
  match refl (ES.goal_as_equiv s) s with
    | `True         -> []
    | `NoRefl       -> soft_failure (Tactics.NoRefl)
    | `NoReflMacros -> soft_failure (Tactics.NoReflMacros)

let () =
  T.register "refl"
    ~tactic_help:{general_help = "Closes a reflexive goal.";
                  detailed_help = "A goal is reflexive when the left and right \
                                   frame corresponding to the bi-terms are \
                                   identical. This of course needs to be the \
                                   case also for macros expansions.";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    (only_equiv refl_tac)

(*------------------------------------------------------------------*)
let do_case_tac (args : Args.parser_arg list) s : sequent list =
  match Args.convert_as_lsymb args with
  | Some str when Hyps.mem_name (L.unloc str) s ->
    let id, _ = Hyps.by_name str s in
    List.map (fun (LT.CHyp _, ss) -> ss) (LT.hypothesis_case ~nb:`Any id s)

  | _ ->
    match LT.convert_args s args Args.(Sort ETerm) with
    | Args.Arg (ETerm (ty, f, _)) ->
      begin
        match Type.kind ty with
        | Type.KTimestamp -> LT.timestamp_case f s

        | Type.KMessage -> bad_args ()
        | Type.KIndex -> bad_args ()
      end
    | _ -> bad_args ()


let case_tac args = LT.wrap_fail (do_case_tac args)

let () =
  T.register_general "case"
    ~tactic_help:
      {general_help = "Perform a case analysis.";
       detailed_help = "";
       usages_sorts = [Sort Args.Timestamp;
                       Sort Args.String;];
       tactic_group = Logical}
    (pure_equiv_arg case_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "clear"
    ~tactic_help:{
      general_help = "Clear an hypothesis.";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    (pure_equiv_arg LT.clear_tac)

(*------------------------------------------------------------------*)
(** For each element of the biframe, checks that it is a member of the
  * hypothesis biframe. If so, close the goal. *)
let assumption s =
  let goal = ES.goal s in

  let in_atom =
    (* For equivalence goals, we look for inclusion of the goal in
       an existing equivalence hypothesis *)
    if ES.goal_is_equiv s then
      let goal = ES.goal_as_equiv s in
      (function
        | Equiv.Equiv equiv  ->
          List.for_all (fun elem -> List.mem elem equiv) goal
        | Equiv.Reach _ -> false)

    else (fun at -> Equiv.Atom at = goal)
  in

  let in_hyp _ = function
    | Equiv.Atom at -> in_atom at
    | Equiv.Impl _ as f -> f = goal
    | Equiv.Quant _ as f -> f = goal
  in

  if Hyps.exists in_hyp s
  then []
  else Tactics.soft_failure Tactics.NotHypothesis

let () =
  T.register "assumption"
    ~tactic_help:{general_help = "look for the goal in the hypotheses.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    (only_equiv assumption)

(*------------------------------------------------------------------*)
let byequiv s =
  [Goal.Trace (ES.trace_seq_of_equiv_seq s)]

let () =
  T.register "byequiv"
    ~tactic_help:{general_help = "transform an equivalence goal into a \
                                  reachability goal.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    (only_equiv byequiv)

(*------------------------------------------------------------------*)
let () =
  T.register_general "revert"
    ~tactic_help:{
      general_help = "Take an hypothesis H, and turns the conclusion C into the \
                      implication H => C.";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    (pure_equiv_arg LT.revert_tac)

(*------------------------------------------------------------------*)
(* TODO: simplification function does nothing for now. Use [auto] instead once 
   types are compatible. *)
let simpl_ident : LT.f_simpl = fun ~strong ~close s sk fk -> 
  if close then fk (None, GoalNotClosed) else sk [s] fk

let () =
  T.register_general "intro"
    ~tactic_help:{
      general_help = "Introduce topmost connectives of conclusion \
                      formula, when it can be done in an invertible, \
                      non-branching fashion.\
                      \n\nUsage: intro a b _ c *";
      detailed_help = "";
      usages_sorts = [];
      tactic_group = Logical}
    (pure_equiv_arg (LT.intro_tac simpl_ident))

(*------------------------------------------------------------------*)
let () =
  T.register_general "remember"
    ~tactic_help:{
      general_help = "substitute a term by a fresh variable";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    (pure_equiv_arg LT.remember_tac)

(*------------------------------------------------------------------*)
(** [tautology f s] tries to prove that [f] is always true in [s]. *)
let rec tautology f s = match f with
  | Equiv.Impl (f0,f1) ->
    let s = Hyps.add Args.AnyName f0 s in
    tautology f1 s
  | Equiv.Quant _ -> false
  | Equiv.(Atom (Equiv e)) -> refl e s = `True
  | Equiv.(Atom (Reach _)) ->
    let s = ES.set_goal f s in
    let trace_s = ES.trace_seq_of_equiv_seq s in
    (* TODO: improve automation by doing more than just constraint solving ? *)
    TraceTactics.constraints trace_s

(** [form_simpl_impl f s] simplifies the formula [f] in [s], by trying to
    prove [f]'s hypotheses in [s]. *)
let rec form_simpl_impl f s = match f with
  | Equiv.Impl (f0, f1) ->
    if tautology f0 s then form_simpl_impl f1 s else f
  | _ -> f

let simpl_impl s =
  Hyps.mapi (fun id f ->
      let s_minus = Hyps.remove id s in
      form_simpl_impl f s_minus
    ) s

(*------------------------------------------------------------------*)
let () =
  T.register_general "generalize"
    ~tactic_help:{
      general_help = "Generalize the goal on some terms";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    (pure_equiv_arg (LT.generalize_tac ~dependent:false))

let () =
  T.register_general "generalize dependent"
    ~tactic_help:{
      general_help = "Generalize the goal and hypotheses on some terms";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    (pure_equiv_arg (LT.generalize_tac ~dependent:true))

(*------------------------------------------------------------------*)
let () =
  T.register_general "apply"
    ~tactic_help:{
      general_help=
        "Matches the goal with the conclusion of the formula F provided \
         (directly, using lemma, or using an axiom), trying to instantiate \
         F variables. Creates one subgoal for each premises of F.\n\
         Usage: apply my_lem.\n       \
         apply my_axiom.\n       \
         apply (forall (x:message), F => G).";
      detailed_help="";
      usages_sorts=[];
      tactic_group=Structural}
    (pure_equiv_arg LT.apply_tac)

(*------------------------------------------------------------------*)
(** [generalize ts s] reverts all hypotheses that talk about [ts] in [s],
    by introducing them in the goal.
    Also returns a function that introduce back the generalized hypothesis.*)
let generalize (ts : Term.timestamp) s =
  let ts = match ts with
    | Var t -> (Vars.EVar t)
    | _ -> hard_failure (Failure "timestamp is not a var") in

  let gen_hyps = Hyps.fold (fun id f gen_hyps ->
      if Sv.mem ts (Equiv.fv f)
      then id :: gen_hyps
      else gen_hyps
    ) s [] in

  (* generalized sequent *)
  let s = List.fold_left (fun s id -> LT.revert id s) s gen_hyps in

  (* function introducing back generalized hypotheses *)
  let intro_back s =
    let ips = List.rev_map (fun id ->
        let ip = Args.Named (Ident.name id) in
        Args.(Simpl (SNamed ip))
      ) gen_hyps in
    Utils.as_seq1 (LT.do_intros_ip simpl_ident ips s) in

  intro_back, s


(*------------------------------------------------------------------*)
(** Given a judgement [s] of the form Γ ⊢ E, and a timestamp τ,
    produce the judgments
    Γ ⊢ E{ts → init}   and   (Γ, E{ts → pred τ}) ⊢ E.
    The second one is then direclty simplified by a case on all possible
    values of τ, producing a judgement for each one.
    Generalizes Γ ⊢ E over τ if necessary. *)
let induction Args.(Timestamp ts) s =
  let env = ES.env s in
  match ts with
  | Var t as ts ->
    (* Generalizes over [ts]. *)
    let intro_back, s = generalize ts s in

    (* Remove ts from the sequent, as it will become unused. *)
    let s = ES.set_env (Vars.rm_var env t) s in
    let table  = ES.table s in
    let system = ES.system s in
    let subst = [Term.ESubst (ts, Pred ts)] in
    let goal = ES.goal s in

    let ind_hyp = Equiv.subst subst goal in
    let id_ind, induc_s = Hyps.add_i Args.Unnamed ind_hyp s in
    (* intro back generalized hyps *)
    let induc_s = intro_back induc_s in
    (* rename the inducition hypothesis *)
    let induc_s = LT.do_naming_pat (`Hyp id_ind) Args.AnyName induc_s in

    let init_goal = Equiv.subst [Term.ESubst(ts,Term.init)] goal in
    let init_s = ES.set_goal init_goal s in
    let init_s = intro_back init_s in

    let goals = ref [] in
    (** [add_action _action descr] adds to goals the goal corresponding to the
      * case where [t] is instantiated by [descr]. *)
    let add_action descr =
      if descr.Action.name = Symbols.init_action
      then ()
      else
        begin
          let env = ref @@ ES.env induc_s in
          let subst =
            List.map
              (fun i ->
                 let i' = Vars.fresh_r env i in
                 Term.ESubst (Term.Var i, Term.Var i'))
              descr.Action.indices
          in
          let name =
            SystemExpr.action_to_term table system
              (Action.subst_action subst descr.Action.action)
          in
          let ts_subst = [Term.ESubst(ts,name)] in
          goals := (ES.subst ts_subst induc_s
                    |> ES.set_env !env)
                   ::!goals
        end
    in

    SystemExpr.iter_descrs table system add_action ;

    List.map simpl_impl (init_s :: List.rev !goals)

  | _  ->
    soft_failure
      (Tactics.Failure "expected a timestamp variable")

let () =
  T.register_typed "induction"
    ~general_help:"Apply the induction scheme to the given timestamp."
    ~detailed_help:"Given a timestamp ts, that does not occur in the hypothesis, \
                    it creates two sub-goals, one where ts has been replaced by \
                    init, and one where we assume that the goal holds on \
                    pred(ts)."
    ~tactic_group:Logical
    (pure_equiv_typed induction) Args.Timestamp

(*------------------------------------------------------------------*)
let enrich (arg : Theory.eterm Args.arg) (s : ES.t) =
  match arg with
  | Args.ETerm (ty, f, loc) ->
    let elem : Term.message =
      match Type.equalk_w (Term.kind f) Type.KMessage with
      | Some Type.Type_eq -> f
      | None -> hard_failure (Tactics.Failure "expected a message")
    in
    ES.set_equiv_goal (elem :: ES.goal_as_equiv s) s

let enrich_a arg s =
  let tbl, env = ES.table s, ES.env s in
  match Args.convert_args tbl (ES.ty_vars s) env [arg] Args.(Sort ETerm) with
  | Args.Arg (ETerm _ as arg) -> enrich arg s
  | _ -> bad_args ()

let enrichs args s =
  List.fold_left (fun s arg -> enrich_a arg s) s args

let enrich_tac args s sk fk =
  try sk [enrichs args s] fk with
  | Tactics.Tactic_soft_failure e -> fk e

let () =
  T.register_general "enrich"
    ~tactic_help:{
      general_help  = "Enrich the goal with the given term.";
      detailed_help = "This is usually called before the induction, to enrich the \
                       induction hypothesis, and then allow to solve multiple cases \
                       more simply.";
      tactic_group  = Logical;
      usages_sorts  = [Sort Args.Message; Sort Args.Boolean]; }
    (pure_equiv_arg enrich_tac)


(*------------------------------------------------------------------*)
let print_tac Args.None s =
  Tactics.print_system (ES.table s) (ES.system s);
  [s]

let () =
  T.register_typed "print" ~general_help:"Shows the current system."
    ~detailed_help:""
    ~tactic_group:Logical
    (pure_equiv_typed print_tac) Args.None


(*------------------------------------------------------------------*)
(** {2 Structural Tactics} *)

(* not very useful in equivalence mode *)
let () =
  T.register_typed "depends"
    ~general_help:"If the second action depends on the first \
                   action, and if the second \
                   action happened, \
                   add the corresponding timestamp inequality."
    ~detailed_help:"Whenever action A1[i] must happen before A2[i], if A2[i] \
                    occurs in the trace, we can add A1[i]. "
    ~tactic_group:Structural
    (pure_equiv_typed LT.depends) Args.(Pair (Timestamp, Timestamp))


(*------------------------------------------------------------------*)
(** Function application *)

exception No_common_head
exception No_FA

let fa_expand t =
  let aux : type a. a Term.term -> Equiv.equiv = function
    | Fun (f,_,[c;t;e]) when f = Term.f_ite && t = e ->
      ES.[ t ]

    | Fun (f,_,l) -> l

    | Atom (`Message (_,f,g)) ->
      ES.[ f ; g ]

    | Diff _ -> raise No_common_head
    | _ -> raise No_FA
  in

  (* FIXME: this may no longer be necessary (type changes) *)
  (* Remve of_bool(b) coming from expansion of frame macro *)
  let filterBoolAsMsg =
    List.map
      (fun x -> match x with
         | Term.Fun (f,_,[c])
           when f = Term.f_of_bool -> c
         | _ -> x)
  in
  filterBoolAsMsg (aux (Term.head_normal_biterm t))

let fa Args.(Int i) s =
  let before, e, after = split_equiv_goal i s in
  try
    (* Special case for try find, otherwise we use fa_expand *)
    match e with
    | Find (vars,c,t,e) ->
      let env = ref (ES.env s) in
      let vars' = List.map (Vars.fresh_r env) vars in
      let subst =
        List.map2
          (fun i i' -> Term.ESubst (Term.Var i, Term.Var i'))
          vars vars'
      in
      let c' = Term.(Seq (vars, c)) in
      let t' = Term.subst subst t in
      let biframe =
        List.rev_append before
          (Equiv.[ c' ; t' ; e ] @ after)
      in
      [ ES.set_env !env (ES.set_equiv_goal biframe s) ]
    | _ ->
      let biframe =
        List.rev_append before (fa_expand e @ after) in
      [ ES.set_equiv_goal biframe s ]
  with
  | No_common_head ->
    soft_failure (Tactics.Failure "No common construct")
  | No_FA ->
    soft_failure (Tactics.Failure "FA not applicable")

let () =
  T.register_typed "fa"
    ~general_help:"Break function applications on the nth term of the sequence."
    ~detailed_help:"To prove that a goal containing f(u1,...,un) is \
                    diff-equivalent, one can prove that the goal containing the \
                    sequence u1,...,un is diff-equivalent."
    ~tactic_group:Structural
    (pure_equiv_typed fa) Args.Int

(*------------------------------------------------------------------*)
(** Check if an element appears twice in the biframe,
  * or if it is [input\@t] with some [frame\@t'] appearing in the frame
  * with [pred(t) <= t'] guaranteed,
  * or if it is [exec\@t] with some [frame\@t'] appearing in the frame
  * with [t <= t'] guaranteed. *)
let is_dup table elem elems =
  if List.mem elem elems then true
  else
    let rec leq t t' = let open Term in match t,t' with
      | t,t' when t=t' -> true
      | Pred t, Pred t'-> leq t t'
      | Pred t, t' -> leq t t'
      | Action (n,is), Action (n',is') ->
          Action.(depends (of_term n is table) (of_term n' is' table))
      | _ -> false
    in
    match elem with
      | Term.Macro (im,[],t) when im = Term.in_macro ->
          List.exists
            (function
               | Term.Macro (fm,[],t')
                 when fm = Term.frame_macro && leq (Pred t) t' -> true
               | _ -> false)
            elems
      | Term.Macro (em,[],t) when em = Term.exec_macro ->
          List.exists
            (function
               | Term.Macro (fm,[],t')
                 when fm = Term.frame_macro && leq t t' -> true
               | _ -> false)
            elems
      | _ -> false

(** This function goes over all elements inside elems.  All elements that can be
   seen as duplicates, or context of duplicates, are removed. All elements that
   can be seen as context of duplicates and assumptions are removed, but
   replaced by the assumptions that appear as there subterms. *)
let rec filter_fa_dup table res assump (elems : Equiv.equiv) =
  let rec is_fa_dup acc elems e =
    (* if an element is a duplicate wrt. elems, we remove it directly *)
    if is_dup table e elems then
      (true,[])
    (* if an element is an assumption, we succeed, but do not remove it *)
    else if List.mem e assump then
      (true,[e])
    (* otherwise, we go recursively inside the sub-terms produced by function
       application *)
    else try
      let new_els = fa_expand e in
      List.fold_left
        (fun (aux1,aux2) e ->
          let (fa_succ,fa_rem) = is_fa_dup acc elems e in
          fa_succ && aux1, fa_rem @ aux2)
        (true,[]) new_els
    with No_FA | No_common_head -> (false,[])
  in
  match elems with
  | [] -> res
  | e :: els ->
    let (fa_succ,fa_rem) =  is_fa_dup [] (res@els) e in
    if fa_succ then filter_fa_dup table (fa_rem@res) assump els
    else filter_fa_dup table (e::res) assump els

(** This tactic filters the biframe through filter_fa_dup, passing the set of
   hypotheses to it.  This is applied automatically, and essentially leaves only
   assumptions, or elements that contain a subterm which is neither a duplicate
   nor an assumption. *)
let fa_dup s =
  let table = ES.table s in

  (* TODO: allow to choose the hypothesis through its id *)
  let hyp = Hyps.find_map (fun _id hyp -> match hyp with
      | Equiv.(Atom (Equiv e)) -> Some e
      | _ -> None) s in

  let hyp = Utils.odflt [] hyp in

  let biframe = ES.goal_as_equiv s
                |> List.rev
                |> filter_fa_dup table [] hyp
  in
  [ES.set_equiv_goal biframe s]

exception Not_FADUP_formula
exception Not_FADUP_iter

class check_fadup ~(cntxt:Constr.trace_cntxt) tau = object (self)

  inherit [Term.timestamp list] Iter.fold ~cntxt as super

  method check_formula f = ignore (self#fold_message [Term.Pred tau] f)

  method extract_ts_atoms phi =
    List.partition
      (function Term.Atom (`Timestamp _) -> true | _ -> false)
      (Term.decompose_ands phi)

  method add_atoms atoms timestamps =
    List.fold_left
      (fun acc at -> match at with
        | Term.Atom (`Timestamp (`Leq,tau_1,tau_2)) ->
          if List.mem tau_2 acc
          then tau_1::acc
          else acc
        | Atom (`Timestamp (`Lt,tau_1,tau_2)) ->
          if (List.mem (Term.Pred tau_2) acc || List.mem tau_2 acc)
          then tau_1::acc
          else acc
        | _ -> raise Not_FADUP_iter)
      timestamps
      atoms

  method fold_message timestamps t = match t with
    | Macro (ms,[],a)
      when (ms = Term.in_macro && (a = tau || List.mem a timestamps)) ||
           (ms = Term.out_macro && List.mem a timestamps) ->
      timestamps

    | Fun (f,_, [Macro (ms,[],a);then_branch; _])
      when f = Term.f_ite && ms = Term.exec_macro && List.mem a timestamps ->
      self#fold_message timestamps then_branch

    | Fun (f, _, [phi_1;phi_2]) when f = Term.f_impl ->
      let atoms,l = self#extract_ts_atoms phi_1 in
      let ts' = self#add_atoms atoms timestamps in
      List.iter
        (fun phi -> ignore (self#fold_message ts' phi))
        (phi_2::l) ;
      timestamps

    | Fun (f, _, _) when f = Term.f_and ->
      let atoms,l = self#extract_ts_atoms t in
      let ts' = self#add_atoms atoms timestamps in
      List.iter
        (fun phi -> ignore (self#fold_message ts' phi))
        l ;
      timestamps

    | Atom (`Index _) | Atom (`Timestamp _) -> timestamps

    | Fun _ | Seq _ | Find _
    | Atom (`Message _)
    | ForAll _ | Exists _ -> super#fold_message timestamps t

    | Macro _ | Name _ | Var _ | Diff _
    | Atom (`Happens _) -> raise Not_FADUP_iter
end

let fa_dup_int i s =
  let before, e, after = split_equiv_goal i s in

  let biframe_without_e = List.rev_append before after in
  let cntxt = ES.mk_trace_cntxt s in
  try
    (* we expect that e is of the form exec@pred(tau) && phi *)
    let (tau,phi) =
      let f,g = match e with
        | Term.Fun (fs,_, [f;g]) when fs = Term.f_and -> f,g

        | Term.Seq (vars, Term.Fun (fs,_, [f;g])) when fs = Term.f_and ->
          let _, subst = Term.refresh_vars `Global vars in
          Term.subst subst f,
          Term.subst subst g

        | _ -> raise Not_FADUP_formula
      in

      match f,g with
      | (Term.Macro (fm,[], Term.Pred tau), phi) when fm = Term.exec_macro
        -> (tau,phi)
      | (phi, Term.Macro (fm,[], Term.Pred tau)) when fm = Term.exec_macro
        -> (tau,phi)
      | _ -> raise Not_FADUP_formula
    in

    let frame_at_pred_tau =
      Term.Macro (Term.frame_macro,[],Term.Pred tau)
    in
    (* we first check that frame@pred(tau) is in the biframe *)
    if not (List.mem frame_at_pred_tau biframe_without_e) then
      raise Not_FADUP_formula;

    (* we iterate over the formula phi to check if it contains only
     * allowed subterms *)
    let iter = new check_fadup ~cntxt tau in
    iter#check_formula phi ;
    (* on success, we keep only exec@pred(tau) *)
    let new_elem = Term.Macro (Term.exec_macro,[],Term.Pred tau) in

    [ES.set_equiv_goal (List.rev_append before (new_elem::after)) s]

  with
  | Not_FADUP_formula ->
    soft_failure (Tactics.Failure "can only apply the tactic on \
                                   a formula of the form (exec@pred(tau) && phi) \
                                   with frame@pred(tau) in the biframe")

  | Not_FADUP_iter ->
    soft_failure (Tactics.Failure "the formula contains subterms \
                                   that are not handled by the FADUP rule")


let fadup Args.(Opt (Int, p)) s : ES.sequents =
  match p with
  | None -> fa_dup s
  | Some (Args.Int i) -> fa_dup_int i s

let () =
 T.register_typed "fadup"
   ~general_help:"When applied without argument, tries to remove all terms that \
                  are duplicates, or context of duplicates."
   ~detailed_help: "When applied on a formula of the form (exec@pred(tau) && \
                    phi), with frame@pred(tau) in the biframe, tries to remove \
                    phi if it contains only subterms allowed by the FA-DUP rule."
   ~tactic_group:Structural
   (pure_equiv_typed fadup) Args.(Opt Int)

(*------------------------------------------------------------------*)
(** Fresh *)

(** Construct the formula expressing freshness for some projection. *)
let mk_phi_proj cntxt env (n : Term.nsymb) proj biframe =
  let proj_frame = List.map (Equiv.pi_term proj) biframe in
  begin try
    let list_of_indices_from_frame =
      let iter = new Fresh.get_name_indices ~cntxt false n.s_symb in
        List.iter iter#visit_message proj_frame ;
        iter#get_indices
    and list_of_actions_from_frame =
      let iter = new Fresh.get_actions ~cntxt in
      List.iter iter#visit_message proj_frame ;
      iter#get_actions
    and tbl_of_action_indices = Hashtbl.create 10 in

    SystemExpr.(iter_descrs cntxt.table cntxt.system
      (fun action_descr ->
        let iter = new Fresh.get_name_indices ~cntxt true n.s_symb in
        let descr_proj = Action.pi_descr proj action_descr in
        iter#visit_message (snd descr_proj.condition) ;
        iter#visit_message (snd descr_proj.output) ;
        List.iter (fun (_,t) -> iter#visit_message t) descr_proj.updates;
        (* we add only actions in which name occurs *)
        let action_indices = iter#get_indices in
        if List.length action_indices > 0 then
          Hashtbl.add tbl_of_action_indices descr_proj action_indices));

    (* direct cases (for explicit occurrences of [name] in the frame) *)
    let phi_frame =
        (List.map
           (fun j ->
              (* select bound variables,
               * to quantify universally over them *)
              let bv =
                List.filter
                  (fun i -> not (Vars.mem env i))
                  j
              in
              let env = ref env in
              let bv' =
                List.map (Vars.fresh_r env) bv in
              let subst =
                List.map2
                  (fun i i' -> Term.ESubst (Term.Var i, Term.Var i'))
                  bv bv'
              in
              let j = List.map (Term.subst_var subst) j in
              Term.mk_forall
                (List.map (fun i -> Vars.EVar i) bv')
                (Term.mk_indices_neq n.s_indices j))
           list_of_indices_from_frame)

    (* indirect cases (occurrences of [name] in actions of the system) *)
    and phi_actions =
      Hashtbl.fold
        (fun a indices_a formulas ->
            (* for each action [a] in which [name] occurs
             * with indices from [indices_a] *)
            let env = ref env in
            let new_action_indices =
              List.map
                (fun i -> Vars.fresh_r env i)
                a.Action.indices
            in

            let bv =
              List.filter
                (fun i -> not (List.mem i a.Action.indices))
                (List.sort_uniq Stdlib.compare (List.concat indices_a))
            in

            let bv' =
              List.map
                (fun i -> Vars.fresh_r env i)
                bv
            in

            let subst =
              List.map2
                (fun i i' -> Term.ESubst (Term.Var i, Term.Var i'))
                a.Action.indices new_action_indices @
              List.map2
                (fun i i' -> Term.ESubst (Term.Var i, Term.Var i'))
                bv bv'
            in
            (* apply [subst] to the action and to the list of
             * indices of our name's occurrences *)
            let new_action =
              SystemExpr.action_to_term cntxt.table cntxt.system
                (Action.subst_action subst a.Action.action)
            in

            let indices_a =
              List.map
                (List.map (Term.subst_var subst))
                indices_a
            in

            (* if new_action occurs before an action of the frame *)
            let disj =
              Term.mk_ors
                  (List.map
                    (fun t ->
                      Term.Atom (Term.mk_timestamp_leq new_action t)
                    ) list_of_actions_from_frame)

            (* then indices of name in new_action and of [name] differ *)
            and conj =
              Term.mk_ands
                (List.map
                   (fun is -> Term.mk_indices_neq is n.s_indices)
                   indices_a)
            in
            let forall_var =
              List.map (fun i -> Vars.EVar i) (new_action_indices @ bv') in
            (Term.mk_forall
               forall_var (Term.mk_impl disj conj))::formulas)
        tbl_of_action_indices
        []
    in
    phi_frame @ phi_actions
  with
  | Fresh.Name_found ->
      soft_failure (Tactics.Failure "Name not fresh")
  | Fresh.Var_found ->
      soft_failure
        (Tactics.Failure "Variable found, unsound to apply fresh")
  end

let fresh_cond (cntxt : Constr.trace_cntxt) env t biframe : Term.message =
  let n_left, n_right =
    match Term.pi_term PLeft t, Term.pi_term PRight t with
    | (Name nl, Name nr) -> nl, nr
    | _ -> raise Fresh.Not_name
  in

  let system_left = SystemExpr.(project_system PLeft cntxt.system) in
  let cntxt_left = { cntxt with system = system_left } in
  let phi_left = mk_phi_proj cntxt_left env n_left PLeft biframe in

  let system_right = SystemExpr.(project_system PRight cntxt.system) in
  let cntxt_right = { cntxt with system = system_right } in
  let phi_right = mk_phi_proj cntxt_right env n_right PRight biframe in

  Term.mk_ands
    (* remove duplicates, and then concatenate *)
    ((List.filter (fun x -> not (List.mem x phi_right)) phi_left)
     @
     phi_right)


(** Returns the term [if (phi_left && phi_right) then 0 else diff(nL,nR)]. *)
let mk_if_term cntxt env t biframe =
  let ty = Term.ty t in
  if not Symbols.(check_bty_info cntxt.Constr.table ty Ty_large) then
    soft_failure
      (Failure "name is of a type that is not [large]");

  let phi = fresh_cond cntxt env t biframe in
  let then_branch = Term.mk_zero in
  let else_branch = t in
  Term.(mk_ite phi then_branch else_branch)


let fresh Args.(Int i) s =
  let before, e, after = split_equiv_goal i s in

  (* the biframe to consider when checking the freshness *)
  let biframe = List.rev_append before after in
  let cntxt   = ES.mk_trace_cntxt s in
  let env     = ES.env s in
  match mk_if_term cntxt env e biframe with
  | if_term ->
    let biframe = List.rev_append before (if_term :: after) in
    [ES.set_equiv_goal biframe s]

  | exception Fresh.Not_name ->
    soft_failure
      (Tactics.Failure "Can only apply fresh tactic on names")

let () =
  T.register_typed "fresh"
    ~general_help:"Removes a name if fresh."
    ~detailed_help:"This replaces a name n by the term 'if fresh(n) then zero \
                    else n, where fresh(n) captures the fact that this specific \
                    instance of the name cannot have been produced by another \
                    action.'"
    ~tactic_group:Structural
    (pure_equiv_typed fresh) Args.Int



(*------------------------------------------------------------------*)
(** Sequence expansion of the sequence [term] for the given parameters [ths]. *)
let expand_seq (term : Theory.term) (ths : Theory.term list) (s : ES.t) =
  let env = ES.env s in
  let table = ES.table s in
  match LT.convert_i s term with
  (* we expect term to be a sequence *)
  | (Seq (vs, t) as term_seq), ty ->
    let vs = List.map (fun x -> Vars.EVar x) vs in

    (* we parse the arguments ths, to create a substution for variables vs *)
    let subst = Theory.parse_subst table (ES.ty_vars s) env vs ths in

    (* new_t is the term of the sequence instantiated with the subst *)
    let new_t = Term.subst subst t in

    (* we add the new term to the frame and the hypothesis if it does not yet
       belongs to it *)
    let biframe =
      let old_biframe = ES.goal_as_equiv s in
      if List.mem new_t old_biframe then old_biframe else new_t :: old_biframe
    in

    let rec mk_hyp_f = function
      | Equiv.Atom at       -> Equiv.Atom (mk_hyp_at at)
      | Equiv.Impl (f, f0)  -> Equiv.Impl (mk_hyp_f f, mk_hyp_f f0)
      | Equiv.Quant _ as f -> f

    and mk_hyp_at hyp = match hyp with
      | Equiv.Equiv e ->
        let new_e =
          if not (List.mem new_t e) && List.mem term_seq e
          then new_t :: e
          else e
        in
        Equiv.Equiv new_e

      | Equiv.Reach f -> hyp
    in

    let s = Hyps.map mk_hyp_f s in

    [ ES.set_equiv_goal biframe s]

  | _ ->
    hard_failure
      (Tactics.Failure "can only expand with sequences with parameters")


(*------------------------------------------------------------------*)
let () = T.register_general "expand" 
    ~tactic_help:
      {general_help = "Expand the given macro.";
       detailed_help = "The value of the macro is obtained by looking \
                        at the corresponding action in the \
                        protocol. It cannot be used on macros with \
                        unknown timestamp.";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    (pure_equiv_arg LT.expand_tac)

(*------------------------------------------------------------------*)
let expand_seq args s =
  match args with
  | (Args.Theory v) :: ids ->
    let ids =
      List.map (function
          | Args.Theory th -> th
          | _ -> bad_args ()
        ) ids
    in
    expand_seq v ids s 
  | _ -> bad_args ()

let expand_seq_tac args = LT.wrap_fail (expand_seq args)

(* Does not rely on the typed registration, as it parses a substitution. *)
let () = T.register_general "expandseq"

    ~tactic_help:{general_help = "Expand the given sequence.";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Structural}
    (pure_equiv_arg expand_seq_tac)

(*------------------------------------------------------------------*)
let () = T.register "expandall"
    ~tactic_help:{
      general_help  = "Expand all possible macros in the sequent.";
      detailed_help = "";
      tactic_group  = Structural;
      usages_sorts  = []; }
    (pure_equiv_typed LT.expand_all_l `All)

(*------------------------------------------------------------------*)
let () =
  T.register_general "exists"
    ~tactic_help:
      {general_help = "Introduce the existentially quantified \
                       variables in the conclusion of the judgment, \
                       using the arguments as existential witnesses.\
                       \n\nUsage: exists v1, v2, ...";
       detailed_help = "";
       usages_sorts = [];
       tactic_group = Logical}
    (pure_equiv_arg LT.exists_intro_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "destruct"
    ~tactic_help:{
      general_help = "Destruct an hypothesis. An optional And/Or \
                      introduction pattern can be given.\n\n\
                      Usages: destruct H.\n\
                     \        destruct H as [A | [B C]]";
      detailed_help = "";
      usages_sorts = [];
      tactic_group = Logical}
    (pure_equiv_arg LT.destruct_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "use"
    ~tactic_help:
      {general_help = "Apply an hypothesis with its universally \
                       quantified variables instantiated with the \
                       arguments.\n\n\
                       Usages: use H with v1, v2, ...\n\
                      \        use H with ... as ...";
       detailed_help = "";
       usages_sorts = [];
       tactic_group = Logical}
    (pure_equiv_arg LT.use_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "assert"
    ~tactic_help:
      {general_help = "Add an assumption to the set of hypothesis, \
                       and produce the goal for\
                       \nthe proof of the assumption.\n\
                       Usages: assert f.\n \
                      \       assert f as intro_pat";
       detailed_help = "";
       usages_sorts = [];
       tactic_group = Logical}
    (pure_equiv_arg LT.assert_tac)

(*------------------------------------------------------------------*)
(** Replace all occurrences of [t1] by [t2] inside of [s],
  * and add a subgoal to prove that [t1 <=> t2]. *)
let equiv_formula f1 f2 (s : ES.t) =
  (* goal for the equivalence of t1 and t2 *)
  let f =
    Term.mk_and ~simpl:false
      (Term.mk_impl ~simpl:false f1 f2)
      (Term.mk_impl ~simpl:false f2 f1) in
  let trace_sequent = ES.trace_seq_of_reach f s in

  let subgoals =
    [ Goal.Trace trace_sequent;
      Goal.Equiv
        (ES.subst [Term.ESubst (f1,f2)] s) ]
  in
  subgoals

(** Replace all occurrences of [m1] by [m2] inside of [s],
  * and add a subgoal to prove that [Eq(m1, m2)]. *)
let equiv_message m1 m2 (s : ES.t) =
  (* goal for the equivalence of t1 and t2 *)
  let trace_sequent =
    ES.trace_seq_of_reach (Term.Atom (`Message (`Eq,m1,m2))) s
  in
  let subgoals =
    [ Goal.Trace trace_sequent;
      Goal.Equiv
        (ES.subst [Term.ESubst (m1,m2)] s) ]
  in
  subgoals

(* TODO: subsumed by rewrite *)
let equivalent arg s = match arg with
  | Args.Pair (t1,t2) ->
    match t1, t2 with
    | Args.ETerm (ty1, f1, _), Args.ETerm (ty2, f2, _) ->
      match Type.kind ty1, Type.kind ty2 with
      | Type.KMessage, Type.KMessage when ty1 = ty2 ->
        (* TODO: subtypes: unify ty1 and ty2 *)
        if ty1 = Type.Boolean
        then equiv_formula f1 f2 s
        else equiv_message f1 f2 s

      | _ ->
        hard_failure
          (Tactics.Failure ("expected a pair of messages of the same types"))

let () = T.register_typed "equivalent"
    ~general_help:"Replace all occurrences of a formula by another, and ask to \
                   prove that they are equivalent."
    ~detailed_help:"This can be used on messages equality or formulas \
                    equivalence."
    ~tactic_group:Structural
    ~usages_sorts:[Args.(Sort (Pair (Message, Message)));
                   Args.(Sort (Pair (Boolean, Boolean)))]
    (only_equiv_typed equivalent)
    Args.(Pair (ETerm, ETerm))


(*------------------------------------------------------------------*)
let simplify_ite b s cond positive_branch negative_branch =
  if b then
    (* replace in the biframe the ite by its positive branch *)
    (* ask to prove that the cond of the ite is True *)
    let trace_s = ES.trace_seq_of_reach cond s in
    (positive_branch, trace_s)
  else
    (* replace in the biframe the ite by its negative branch *)
    (* ask to prove that the cond of the ite implies False *)
    let trace_s = ES.trace_seq_of_reach (Term.mk_impl cond Term.mk_false) s in
    (negative_branch, trace_s)


let get_ite ~cntxt elem =
  match Iter.get_ite_term cntxt elem with
  | [] -> None
  | occ :: _ ->
    (* Context with bound variables (eg try find) are not supported. *)
    if not (Sv.is_empty occ.Iter.occ_vars) then
      soft_failure (Tactics.Failure "cannot be applied in a under a binder");

    Some (occ.Iter.occ_cnt)

let yes_no_if b Args.(Int i) s =
  let cntxt = ES.mk_trace_cntxt s in

  let before, elem, after = split_equiv_goal i s in

  (* search for the first occurrence of an if-then-else in [elem] *)
  match get_ite ~cntxt elem with
  | None ->
    soft_failure
      (Tactics.Failure
         "can only be applied on a term with at least one occurrence
          of an if then else term")

  | Some (c,t,e) ->
    let branch, trace_sequent = simplify_ite b s c t e in
    let new_elem =
      Equiv.subst_equiv
        [Term.ESubst (Term.mk_ite ~simpl:false c t e,branch)]
        [elem]
    in
    let biframe = List.rev_append before (new_elem @ after) in
    [ Goal.Trace trace_sequent;
      Goal.Equiv (ES.set_equiv_goal biframe s) ]

let () =
 T.register_typed "noif"
   ~general_help:"Try to prove diff equivalence by proving that the condition at \
                  the i-th position implies False."
   ~detailed_help:"Replaces a proof goal with `if phi then u else v` by the \
                   goals 'phi <=> false' and the original goal now with v \
                   instead of the conditional."
   ~tactic_group:Structural
   (only_equiv_typed (yes_no_if false)) Args.Int

let () =
 T.register_typed "yesif"
   ~general_help:"Try to prove diff equivalence by proving that the condition at \
                  the i-th position is True."
   ~detailed_help:"Replaces a proof goal with `if phi then u else v` by the \
                   goals 'phi <=> true' and the original goal now with u \
                   instead of the conditional."
   ~tactic_group:Structural
   (only_equiv_typed (yes_no_if true)) Args.Int

(*------------------------------------------------------------------*)
exception Not_ifcond

(** Push the formula [f] in the message [term].
  * Goes under function symbol, diff, seq and find. If [j]=Some jj, will push
  * the formula only in the jth subterm of the then branch (if it exists,
  * otherwise raise an error). *)
let push_formula (j: 'a option) f term =
  let f_vars = Term.get_vars f in
  let not_in_f_vars vs =
    List.fold_left
      (fun acc v ->
         if List.mem (Vars.EVar v) f_vars
         then false
         else acc)
      true
      vs
  in

  let rec mk_ite m = match m with
    (* if c then t else e becomes if (f => c) then t else e *)
    | Term.Fun (fs,_,[c;t;e]) when fs = Term.f_ite ->
      Term.mk_ite ~simpl:false (Term.mk_impl ~simpl:false f c) t e

    (* m becomes if f then m else 0 *)
    | _ -> Term.mk_ite ~simpl:false f m Term.mk_zero
  in

  match term with
  | Term.Fun (f, _, _) when f = Term.f_ite -> mk_ite term

  | Term.Fun (f, fty, terms) ->
    begin match j with
      | None -> Fun (f, fty, List.map mk_ite terms)
      | Some (Args.Int jj) ->
        if jj < List.length terms then
          Fun (f, fty, List.mapi (fun i t -> if i=jj then mk_ite t else t) terms)
        else
          soft_failure
            (Tactics.Failure "subterm at position j does not exists")
    end

  | Term.Diff (a, b) ->
    begin match j with
      | None -> Diff (mk_ite a, mk_ite b)
      | Some (Args.Int 0) -> Diff (mk_ite a, b)
      | Some (Args.Int 1) -> Diff (a, mk_ite b)
      | _ ->  soft_failure
                (Tactics.Failure "expected j is 0 or 1 for diff terms")
    end

  | Term.Seq (vs, t) ->
    if not_in_f_vars vs then Seq (vs, mk_ite t)
    else raise Not_ifcond

  | Term.Find (vs, b, t, e) ->
    if not_in_f_vars vs then Find (vs, b, mk_ite t, mk_ite e)
    else raise Not_ifcond

  | _ -> mk_ite term

let ifcond Args.(Pair (Int i, Pair (Opt (Int, j), Boolean f))) s =
  let before, e, after = split_equiv_goal i s in

  let cond, positive_branch, negative_branch =
    match e with
    | Term.Fun (fs,_,[c;t;e]) when fs = Term.f_ite -> (c, t, e)
    | _ ->  soft_failure
              (Tactics.Failure "can only be applied to a conditional")
  in

  try
    let new_elem = 
      Term.mk_ite ~simpl:false
        cond (push_formula j f positive_branch) negative_branch
    in
    let biframe = List.rev_append before (new_elem :: after) in
    let trace_sequent = 
      ES.trace_seq_of_reach Term.(mk_impl ~simpl:false cond f) s 
    in

    [ Goal.Trace trace_sequent;
      Goal.Equiv (ES.set_equiv_goal biframe s) ]
  with
  | Not_ifcond ->
    soft_failure 
      (Tactics.Failure "the formula contains variables that overlap with \
                        variables bound by \
                        a seq or a try find construct")


let () =
  T.register_typed "ifcond"
    ~general_help: "If the given conditional implies that the given formula f is \
                    true, push the formula f at top-level in all the subterms of \
                    the then branch. "
    ~detailed_help:"A message m in the positive branch will become of the form \
                    `if f then m else 0`. If the int parameter j is given, will \
                    push the formula only in the jth subterm of the then branch \
                    (zero-based)."
   ~tactic_group:Structural
   (only_equiv_typed ifcond) Args.(Pair (Int, Pair( Opt Int, Boolean)))


(*------------------------------------------------------------------*)
(* TODO: should be a rewriting rule *)
let trivial_if (Args.Int i) (s : ES.sequent) =
  let cntxt = ES.mk_trace_cntxt s in

  let before, elem, after = split_equiv_goal i s in

  (* search for the first occurrence of an if-then-else in [elem] *)
  match get_ite ~cntxt elem with
  | None ->
    soft_failure
      (Tactics.Failure
         "can only be applied on a term with at least one occurrence \
          of an if then else term")
  | Some (c,t,e) ->
    let trace_seq = 
      ES.trace_seq_of_reach (Term.Atom (`Message (`Eq,t,e))) s
    in
    let trace_goal  = Goal.Trace trace_seq in

    let new_elem =
      Equiv.subst_equiv
        [Term.ESubst (Term.mk_ite c t e,t)]
        [elem]
    in
    let biframe = List.rev_append before (new_elem @ after) in
    [ trace_goal;
      Goal.Equiv (ES.set_equiv_goal biframe s) ]

let () =
 T.register_typed "trivialif"
   ~general_help:"Simplify a conditional when the two branches are equal."
   ~detailed_help:""
   ~tactic_group:Structural
   (only_equiv_typed trivial_if) Args.Int


(*------------------------------------------------------------------*)
(* TODO: should be a rewriting rule *)
let ifeq Args.(Pair (Int i, Pair (Message (t1,ty1), Message (t2,ty2)))) s =

  (* check that types are equal *)
  LT.check_ty_eq ty1 ty2;

  let before, e, after = split_equiv_goal i s in

  let cond, positive_branch, negative_branch =
    match e with
    | Term.Fun (fs,_,[c;t;e]) when fs = Term.f_ite -> (c, t, e)
    | _ -> soft_failure
             (Tactics.Failure "Can only be applied to a conditional.")
  in
  let new_elem =
    Term.mk_ite 
      cond
      (Term.subst [Term.ESubst (t1,t2)] positive_branch)
      negative_branch
  in
  let biframe = List.rev_append before (new_elem :: after) in

  let trace_s = 
    ES.trace_seq_of_reach 
      (Term.mk_impl ~simpl:false cond Term.(Atom (`Message (`Eq,t1,t2)))) s
  in

  [ Goal.Trace trace_s;
    Goal.Equiv (ES.set_equiv_goal biframe s) ]

let () = T.register_typed "ifeq"
    ~general_help:"If the given conditional implies the equality of the two \
                   given terms, substitute the first one by the second one \
                   inside the positive branch of the conditional."

    ~detailed_help:"This asks to prove that the equality is indeed implied by \
                    the condition, we can then replace any term by its equal \
                    term (with over-whelming probability) in the positive \
                    brannch."
    ~tactic_group:Structural
    (only_equiv_typed ifeq) Args.(Pair (Int, Pair (Message, Message)))


(*------------------------------------------------------------------*)
(** Automatic simplification *)

let auto ~close ~strong s sk (fk : Tactics.fk) =
  let open Tactics in
  match s with
  | Goal.Equiv s ->
    let sk l _ =
      if close && l <> []
      then fk (None, GoalNotClosed)
      else sk (List.map (fun s -> Goal.Equiv s) l) fk 
    in
    let fk _ =
      if close
      then fk (None, GoalNotClosed)
      else sk [s] fk 
    in

    let wfadup s sk fk =
      let fk _ = sk [s] fk in
      LT.wrap_fail (fadup (Args.Opt (Args.Int, None))) s sk fk 
    in

    let conclude s sk fk  =
      if close || Config.auto_intro () then
        orelse_list [LT.wrap_fail refl_tac;
                     LT.wrap_fail assumption] s sk fk
      else fk (None, GoalNotClosed)
    in

    let reduce s sk fk = sk [LT.reduce_sequent s] fk in

    andthen_list ~cut:true
      [try_tac reduce;
       try_tac wfadup;       
       try_tac
         (andthen_list ~cut:true
            [LT.wrap_fail (LT.expand_all_l `All);
             try_tac wfadup;
             conclude])]
      s sk fk

  | Goal.Trace t ->
    let sk l fk = sk (List.map (fun s -> Goal.Trace s) l) fk in
    TraceTactics.simpl ~close ~strong t sk fk

let tac_auto ~close ~strong args s sk (fk : Tactics.fk) =
   auto ~close ~strong s sk fk

let () =
  T.register_general "auto"
    ~tactic_help:{general_help = "Automatically proves the goal.";
                  detailed_help = "Same as simpl.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural }
    (tac_auto ~close:true  ~strong:true)

let () =
  T.register_general "simpl"
    ~tactic_help:{general_help = "Automatically simplify the goal.";
                  detailed_help = "This tactics automatically calls fadup, \
                                   expands the macros, and closes goals using \
                                   refl or assumption.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural }
    (tac_auto ~close:false ~strong:true)


let () =
  T.register_general "autosimpl"
    ~tactic_help:{general_help = "Automatically simplify the goal.";
                  detailed_help = "This tactics automatically calls fadup, \
                                   expands the macros, and closes goals using \
                                   refl or assumption.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural }
    (tac_auto ~close:false ~strong:false)

(*------------------------------------------------------------------*)
(* TODO: factorize *)
let do_s_item (s_item : Args.s_item) s : Goal.t list =
  match s_item with
  | Args.Simplify l ->
    let tac = auto ~strong:true ~close:false in
    Tactics.run tac s

  | Args.Tryauto l ->
    let tac = Tactics.try_tac (auto ~strong:true ~close:true) in
    Tactics.run tac s

(* TODO: factorize *)
(** Applies a rewrite arg  *)
let do_rw_arg rw_arg rw_in (s : Goal.t) : Goal.t list =
  match rw_arg with
  | Args.R_item rw_item  ->
    begin match s with
      | Goal.Equiv s ->
        let es = LT.do_rw_item rw_item rw_in s in
        List.map (fun x -> Goal.Equiv x) es
      | Goal.Trace s ->
        let ts = TraceTactics.LT.do_rw_item rw_item rw_in s in
        List.map (fun x -> Goal.Trace x) ts
    end
  | Args.R_s_item s_item -> do_s_item s_item s (* targets are ignored there *)

(* TODO: factorize *)
let rewrite_tac args s =
  match args with
  | [Args.RewriteIn (rw_args, in_opt)] ->
    List.fold_left (fun seqs rw_arg ->
        List.concat_map (do_rw_arg rw_arg in_opt) seqs
      ) [s] rw_args

  | _ -> bad_args ()

(* TODO: factorize *)
let rewrite_tac args = wrap_fail (rewrite_tac args)

(* TODO: factorize *)
let () =
  T.register_general "rewrite"
    ~tactic_help:{
      general_help =
        "If t1 = t2, rewrite all occurences of t1 into t2 in the goal.\n\
         Usage: rewrite Hyp Lemma Axiom (forall (x:message), t = t').\n       \
         rewrite Lemma Axiom (t=t').\n       \
         rewrite (forall (x:message), t = t').\n       \
         rewrite (t = t') Lemma in H.";
      detailed_help = "";
      usages_sorts  = [];
      tactic_group  = Structural;}
    rewrite_tac



(*------------------------------------------------------------------*)
(** {2 Cryptographic Tactics} *)

(*------------------------------------------------------------------*)
(** PRF axiom *)

exception Not_hash

type prf_param = {
  h_fn  : Term.fname;
  h_cnt : Term.message;
  h_key : Term.nsymb;
}

let prf_param hash : prf_param =
  match hash with
  | Term.Fun ((h_fn, _), _, [h_cnt; Name h_key]) ->
    { h_fn; h_cnt; h_key }

  | _ -> raise Not_hash

(** [occurrences_of_frame ~cntxt frame hash_fn key_n]
  * returns the list of pairs [is,m] such that [f(m,key_n[is])]
  * occurs in [frame]. Does not explore macros. *)
let occurrences_of_frame ~cntxt frame hash_fn key_n =
  let iter = new Iter.get_f_messages ~cntxt hash_fn key_n in
  List.iter iter#visit_message frame ;
  List.sort_uniq Stdlib.compare iter#get_occurrences

(** [occurrences_of_action_descr ~cntxt action_descr hash_fn key_n]
  * returns the list of pairs [is,m] such that [hash_fn(m,key_n[is])]
  * occurs in [action_descr]. *)
let occurrences_of_action_descr ~cntxt action_descr hash_fn key_n =
  let iter = new Iter.get_f_messages ~cntxt hash_fn key_n in
  iter#visit_message (snd action_descr.Action.output) ;
  List.iter (fun (_,m) -> iter#visit_message m) action_descr.Action.updates ;
  iter#visit_message (snd action_descr.Action.condition) ;
  List.sort_uniq Stdlib.compare iter#get_occurrences

(** direct cases: explicit occurence of the hash in the frame *)
let prf_mk_direct env (param : prf_param) (is, m) =
  (* select bound variables in key indices [is] and in message [m]
     to quantify universally over them *)
  let env = ref env in

  let vars = Term.fv m in
  let vars = Sv.add_list vars is in

  (* we remove the free variables already in [env] from [vars] *)
  let vars = Sv.diff vars (Sv.of_list (Vars.to_list !env)) in

  let vars', subst = Term.erefresh_vars (`InEnv env) (Sv.elements vars) in

  let is = List.map (Term.subst_var subst) is in
  let m = Term.subst subst m in
  Term.mk_forall
    vars'
    (Term.mk_impl
       (Term.mk_indices_eq param.h_key.s_indices is)
       (Term.Atom (`Message (`Neq, param.h_cnt, m))))

(** indirect cases: occurences of hashes in actions of the system *)
let prf_mk_indirect env cntxt (param : prf_param)
    (frame_actions : Fresh.ts_occs) (a, is_m_l) =

  let env = ref env in

  let vars = List.fold_left (fun vars (is, m) ->
      Sv.union (Sv.add_list vars is) (Term.fv m)
    ) Sv.empty is_m_l
  in
  let vars = Sv.union vars (Sv.of_list (List.map Vars.evar a.Action.indices)) in
  let vars = Sv.elements vars in

  let vars, subst = Term.erefresh_vars (`InEnv env) vars in

  (* apply [subst] to the action and to the list of
   * key indices with the hashed messages *)
  let new_action =
    SystemExpr.action_to_term
      cntxt.Constr.table cntxt.system
      (Action.subst_action subst a.Action.action)
  in
  let list_of_is_m =
    List.map (fun (is,m) ->
        (List.map (Term.subst_var subst) is,Term.subst subst m))
      is_m_l in

  (* save the environment after having renamed all free variables until now. *)
  let env0 = !env in
  (* if new_action occurs before a macro timestamp occurence of the frame *)
  let do1 mts_occ =
    let occ_vars = Sv.elements mts_occ.Iter.occ_vars in
    let occ_vars, occ_subst = Term.erefresh_vars (`InEnv (ref env0)) occ_vars in
    let subst = occ_subst @ subst in
    let ts   = Term.subst subst mts_occ.occ_cnt   in
    let cond = Term.subst subst mts_occ.occ_cond in
    Term.mk_exists ~simpl:true occ_vars
      (Term.mk_and
         (Term.Atom (Term.mk_timestamp_leq new_action ts))
         cond)
  in
  let disj = Term.mk_ors (List.map do1 frame_actions) in

  (* then if key indices are equal then hashed messages differ *)
  let conj =
    Term.mk_ands
      (List.map (fun (is,m) ->
           Term.mk_impl
             (Term.mk_indices_eq param.h_key.s_indices is)
             (Term.Atom (`Message (`Neq, param.h_cnt, m))))
          list_of_is_m)
  in

  Term.mk_forall vars (Term.mk_impl disj conj)


let _mk_prf_phi_proj proj (cntxt : Constr.trace_cntxt) env biframe e hash =
  let system = SystemExpr.(project_system proj cntxt.system) in
  let cntxt = { cntxt with system = system } in
  let param = prf_param (Term.pi_term proj hash) in

  (* create the frame on which we will iterate to compute phi_proj
     - e_without_hash is the context where all occurrences of [hash] have
        been replaced by zero
     - we also add the hashed message [t] *)
  let e_without_hash =
    Equiv.subst_equiv [Term.ESubst (hash,Term.mk_zero)] [e]
  in

  let frame =
    param.h_cnt :: (List.map (Equiv.pi_term proj) (e_without_hash @ biframe))
  in

  (* check syntactic side condition *)
  Euf.key_ssc
    ~elems:frame ~allow_functions:(fun x -> false)
    ~cntxt param.h_fn param.h_key.s_symb;

  (* we compute the list of hashes from the frame *)
  let frame_hashes =
    occurrences_of_frame ~cntxt frame param.h_fn param.h_key.s_symb
  in

  let frame_actions =
    let actions =
      List.fold_left (fun acc t ->
          Fresh.get_actions_ext cntxt t @ acc
        ) [] frame
    in
    Fresh.clear_dup_mtso_le actions
  in

  (* we iterate over all the actions of the (single) system *)
  let tbl_of_action_hashes = Hashtbl.create 10 in
  SystemExpr.(iter_descrs cntxt.table cntxt.system (fun action_descr ->
      (* we add only actions in which a hash occurs *)
      let descr_proj = Action.pi_descr proj action_descr in
      let action_hashes =
        occurrences_of_action_descr ~cntxt descr_proj param.h_fn param.h_key.s_symb
      in

      if List.length action_hashes > 0 then
        Hashtbl.add tbl_of_action_hashes descr_proj action_hashes)
    );

  let phi_frame =
    List.map (prf_mk_direct env param) frame_hashes
  in

  let indirect_hashes = Hashtbl.to_list tbl_of_action_hashes in
  let phi_actions =
    List.rev_map
      (prf_mk_indirect env cntxt param frame_actions)
      indirect_hashes 
  in
  Term.mk_ands (phi_frame @ phi_actions)

let mk_prf_phi_proj proj (cntxt : Constr.trace_cntxt) env biframe e hash =
  try _mk_prf_phi_proj proj cntxt env biframe e hash
  with
  | Not_hash -> Term.mk_true
  | Euf.Bad_ssc ->
    soft_failure (Tactics.Failure "key syntactic side condition violated")

(* from two conjonction formula p and q, produce its minimal diff(p, q), of the
   form (p inter q) && diff (p minus q, q minus p) *)
let combine_conj_formulas p q =
  (* we turn the conjonctions into list *)
  let p, q = Term.decompose_ands p, Term.decompose_ands q in
  let aux_q = ref q in
  let (common, new_p) = List.fold_left (fun (common, r_p) p ->
      (* if an element of p is inside aux_q, we remove it from aux_q and add it
         to common, else add it to r_p *)
      if List.mem p !aux_q then
        (aux_q := List.filter (fun e -> e <> p) !aux_q; (p::common, r_p))
      else
        (common, p::r_p))
      ([], []) p
  in
  (* common is the intersection of p and q, aux_q is the remainder of q and
     new_p the remainder of p *)
  Term.mk_and
    (Term.mk_ands common)
    (Term.head_normal_biterm (Term.Diff(Term.mk_ands new_p,
                                        Term.mk_ands !aux_q)))

let prf Args.(Int i) s =
  let before, e, after = split_equiv_goal i s in

  let biframe = List.rev_append before after in
  let cntxt = ES.mk_trace_cntxt s in
  let env = ES.env s in

  let e = Term.head_normal_biterm e in

  (* search for the first occurrence of a hash in [e] *)
  let hash_occ = 
    match Iter.get_ftypes (ES.table s) Symbols.Hash e with
    | [] ->
      soft_failure
        (Tactics.Failure
           "PRF can only be applied on a term with at least one occurrence \
            of a hash term h(t,k)")
        
    | occ :: _ ->
      if not (Sv.is_empty occ.Iter.occ_vars) then
        soft_failure
          (Tactics.Failure "application below a binder is not supported");
      occ
  in

  let fn, ftyp, m, key, hash = match hash_occ.Iter.occ_cnt with
    | Term.Fun ((fn,_), ftyp, [m; key]) as hash ->
      fn, ftyp, m, key, hash
    | _ -> assert false 
  in

  let phi_left  = mk_prf_phi_proj PLeft  cntxt env biframe e hash in
  let phi_right = mk_prf_phi_proj PRight cntxt env biframe e hash in

  (* check that there are no type variables*)
  assert (ftyp.fty_vars = []);

  let nty = ftyp.fty_out in
  let ndef = Symbols.{ n_iarr = 0; n_ty = nty; } in
  let table,n = 
    Symbols.Name.declare cntxt.table (L.mk_loc L._dummy "n_PRF") ndef
  in
  let ns = Term.mk_isymb n nty [] in
  let s = ES.set_table table s in

  let oracle_formula =
    Prover.get_oracle_tag_formula (Symbols.to_string fn)
  in

  let final_if_formula = 
    if Term.is_false oracle_formula 
    then combine_conj_formulas phi_left phi_right
    else 
      let (Vars.EVar uvarm),(Vars.EVar uvarkey),f = 
        match oracle_formula with
        | ForAll ([uvarm;uvarkey],f) -> uvarm,uvarkey,f
        | _ -> assert false
      in
      match Vars.ty uvarm, Vars.ty uvarkey with
      | Type.(Message, Message) -> 
        let f = 
          Term.subst [
            ESubst (Term.Var uvarm, m);
            ESubst (Term.Var uvarkey, key);] f 
        in

        Term.mk_and
          (Term.mk_not f)  
          (combine_conj_formulas phi_left phi_right)

      | _ -> assert false
  in

  let if_term = Term.mk_ite final_if_formula (Term.Name ns) hash in
  let new_elem =
    Equiv.subst_equiv [Term.ESubst (hash,if_term)] [e] 
  in
  let biframe = (List.rev_append before (new_elem @ after)) in
  [ES.set_equiv_goal biframe s]

let () =
  T.register_typed "prf"
    ~general_help:"Apply the PRF axiom."
    ~detailed_help:"It allows to replace a hash h(m,k) by 'if new_hash(m) then \
                    zero else h(m,k)' where new_hash(m) states that m \
                    was never hashed using key k before. Behaves similarly to \
                    the fresh tactic."
    ~tactic_group:Cryptographic
    (pure_equiv_typed prf) Args.Int


(*------------------------------------------------------------------*)
let split_seq (li, ht) s : ES.sequent =
  let i = L.unloc li in
  let before, t, after = split_equiv_goal i s in

  let is, ti = match t with
    | Seq (is, ti) -> is, ti
    | _ -> 
      soft_failure ~loc:(L.loc li) (Failure (string_of_int i ^ " is not a seq"))
  in

  (* check that types are compatible *)
  let seq_hty =
    Type.Lambda (List.map (fun v -> Type.ETy (Vars.ty v)) is, Type.Boolean)
  in

  let hty, ht = LT.convert_ht s ht in

  LT.check_hty_eq hty seq_hty;

  (* compute the new sequent *)
  let is, subst = Term.refresh_vars `Global is in
  let ti = Term.subst subst ti in

  let cond = match Term.apply_ht ht (List.map (fun v -> Term.Var v) is) with
    | Term.Lambda ([], cond) -> cond
    | _ -> assert false
  in

  let ti_t = Term.mk_ite cond               ti Term.mk_zero in
  let ti_f = Term.mk_ite (Term.mk_not cond) ti Term.mk_zero in

  let env = ES.env s in
  let frame = List.rev_append before ([Term.mk_seq env is ti_t; 
                                       Term.mk_seq env is ti_f] @ after) in
  ES.set_equiv_goal frame s

let split_seq_args args s : ES.sequent list =
  match args with
  | [Args.SplitSeq (i, ht)] -> [split_seq (i, ht) s]
  | _ -> bad_args ()

let split_seq_tac args s sk fk = LT.wrap_fail (split_seq_args args) s sk fk

let () =
  T.register_general "splitseq"
    ~tactic_help:{general_help = "splits a sequence according to some boolean";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    (pure_equiv_arg split_seq_tac)

(*------------------------------------------------------------------*)
let const_seq (li, terms) s : Goal.t list =   
  let i = L.unloc li in

  let terms, term_tys = 
    List.split @@
    List.map (fun p_term -> 
        let term, term_ty = LT.convert_i s p_term in
        term, (term_ty, L.loc p_term)
      ) terms
  in

  let before, e, after = split_equiv_goal i s in
  let e_is, e_ti = match e with
    | Seq (is, ti) -> is, ti
    | _ -> 
      soft_failure ~loc:(L.loc li) (Failure (string_of_int i ^ " is not a seq"))
  in

  (* check that types are compatible *)
  List.iter (fun (term_ty, loc) -> 
      LT.check_ty_eq ~loc term_ty (Term.ty e_ti)
    ) term_tys;

  (* refresh variables *)
  let env = ref (ES.env s) in
  let e_is, subst = Term.refresh_vars (`InEnv env) e_is in
  let e_ti = Term.subst subst e_ti in

  let eqs = List.map (fun term ->
      Term.mk_atom `Eq e_ti term
    ) terms
  in
  let cond = 
    Term.mk_forall ~simpl:true (List.map Vars.evar e_is)
      (Term.mk_ors ~simpl:true eqs)
  in
  let s_reach = ES.trace_seq_of_reach cond s in
  
  let frame = List.rev_append before (terms @ after) in
  [ Goal.Trace s_reach;
    Goal.Equiv (ES.set_equiv_goal frame s) ]

let const_seq_args args s : Goal.t list =
  match args with
  | [Args.ConstSeq (i, t)] -> const_seq (i, t) s
  | _ -> bad_args ()

let const_seq_tac args s sk fk = LT.wrap_fail (const_seq_args args) s sk fk

let () =
  T.register_general "constseq"
    ~tactic_help:{general_help = "simplifies a constant sequence";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    (only_equiv_arg const_seq_tac)

(*------------------------------------------------------------------*)
(** Symmetric encryption **)


(** CCA1 *)

let cca1 Args.(Int i) s =
  let before, e, after = split_equiv_goal i s in

  let biframe = List.rev_append before after in
  let cntxt = ES.mk_trace_cntxt s in
  let table = cntxt.table in
  let env = ES.env s in

  let e = Term.head_normal_biterm e in

  let get_subst_hide_enc enc fnenc m fnpk sk fndec r eis is_top_level =
    (* we check that the random is fresh, and the key satisfy the
       side condition. *)

    (* we create the fresh cond reachability goal *)
    let random_fresh_cond = 
      fresh_cond cntxt env (Term.Name r) biframe 
    in

    let fresh_seq = ES.trace_seq_of_reach random_fresh_cond s in
    let fresh_goal = Goal.Trace fresh_seq in

    let new_subst =
      if is_top_level then
        Term.ESubst (enc, Term.mk_len m)
      else
        let new_m = Term.mk_zeroes (Term.mk_len m) in
        let new_term = match fnpk with
          | Some (fnpk,pkis) ->
            Term.mk_fun table fnenc eis
              [new_m; Term.Name r;
               Term.mk_fun table fnpk pkis [Term.Name sk]]

          | None ->
            Term.mk_fun table fnenc eis [new_m; Term.Name r; Term.Name sk]
        in
        Term.ESubst (enc, new_term)
    in
    (fresh_goal, new_subst)
  in

  (* first, we check if the term is an encryption at top level, in which case
     we will completely replace the encryption by the length, else we will
     replace the plain text by the lenght *)
  let is_top_level = match e with
    | Term.Fun ((fnenc,eis), _,
                [m; Term.Name r;
                 Term.Fun ((fnpk,is), _, [Term.Name sk])])
      when (Symbols.is_ftype fnpk Symbols.PublicKey cntxt.table
            && Symbols.is_ftype fnenc Symbols.AEnc table) -> true

    | Term.Fun ((fnenc,eis), _, [m; Term.Name r; Term.Name sk])
      when Symbols.is_ftype fnenc Symbols.SEnc table -> true

    | _ -> false
  in

  (* search for the first occurrence of an asymmetric encryption in [e], that
     do not occur under a decryption symbol. *)
  (* FIXME: Adrien: the description is not accurrate *)
  let rec hide_all_encs (enclist : Iter.mess_occs) = 
    match enclist with
    | [] -> [], []
    | occ :: occs ->
      (* FIXME: check that this is what we want. *)
      if not (Sv.is_empty occ.Iter.occ_vars) then
        soft_failure (Tactics.Failure "cannot be applied in a under a binder");

      match occ.Iter.occ_cnt with
      | (Term.Fun ((fnenc,eis), _, 
                   [m; Term.Name r;
                    Term.Fun ((fnpk,is), _, [Term.Name sk])])
         as enc) 
        when (Symbols.is_ftype fnpk Symbols.PublicKey table
              && Symbols.is_ftype fnenc Symbols.AEnc table) ->
        begin
          match Symbols.Function.get_data fnenc table with
          (* we check that the encryption function is used with the associated
             public key *)
          | Symbols.AssociatedFunctions [fndec; fnpk2] when fnpk2 = fnpk
            ->
            begin
              try
                Euf.key_ssc ~messages:[enc] ~allow_functions:(fun x -> x = fnpk)
                  ~cntxt fndec sk.s_symb;

                if not (List.mem
                          (Term.mk_fun table fnpk is [Term.Name sk])
                          biframe) then
                  soft_failure
                    (Tactics.Failure
                       "The public key must be inside the frame in order to \
                        use CCA1");

                let (fgoals, substs) = hide_all_encs occs in
                let fgoal,subst =
                  get_subst_hide_enc
                    enc fnenc m (Some (fnpk,is)) 
                    sk fndec r eis is_top_level
                in
                (fgoal :: fgoals,subst :: substs)

              with Euf.Bad_ssc ->  soft_failure Tactics.Bad_SSC
            end

          | _ ->
            soft_failure
              (Tactics.Failure
                 "The first encryption symbol is not used with the correct \
                  public key function.")
        end

      | (Term.Fun ((fnenc,eis), _, [m; Term.Name r; Term.Name sk])
         as enc) when Symbols.is_ftype fnenc Symbols.SEnc table
        ->
        begin
          match Symbols.Function.get_data fnenc table with
          (* we check that the encryption function is used with the associated
             public key *)
          | Symbols.AssociatedFunctions [fndec]
            ->
            begin
              try
                Cca.symenc_key_ssc ~elems:(ES.goal_as_equiv s) ~messages:[enc]
                  ~cntxt fnenc fndec sk.s_symb;
                (* we check that the randomness is ok in the system and the
                   biframe, except for the encryptions we are looking at, which
                   is checked by adding a fresh reachability goal. *)
                Cca.symenc_rnd_ssc ~cntxt env fnenc sk biframe;
                let (fgoals, substs) = hide_all_encs occs in
                let fgoal,subst =
                  get_subst_hide_enc enc fnenc m (None) sk fndec r eis is_top_level
                in
                (fgoal :: fgoals,subst :: substs)
              with Euf.Bad_ssc ->  soft_failure Tactics.Bad_SSC
            end
          | _ ->
            soft_failure
              (Tactics.Failure
                 "The first encryption symbol is not used with the correct public \
                  key function.")
        end

      | _ ->
        soft_failure
          (Tactics.Failure
             "CCA1 can only be applied on a term with at least one occurrence \
              of an encryption term enc(t,r,pk(k))")
  in

  let fgoals, substs = 
    hide_all_encs ((Iter.get_ftypes ~excludesymtype:Symbols.ADec
                      table Symbols.AEnc e)
                   @ (Iter.get_ftypes ~excludesymtype:Symbols.SDec
                        table Symbols.SEnc e)) 
  in

  if substs = [] then
    soft_failure
      (Tactics.Failure
         "CCA1 can only be applied on a term with at least one occurrence \
          of an encryption term enc(t,r,pk(k))");

  let new_elem =    Equiv.subst_equiv substs [e] in
  let biframe = (List.rev_append before (new_elem @ after)) in
  Goal.Equiv (ES.set_equiv_goal biframe s) :: fgoals


let () =
  T.register_typed "cca1"
   ~general_help:"Apply the cca1 axiom on all encryptions of the given message."
   ~detailed_help:"Whenever an encryption does not occur under a decryption \
                   symbol and uses a valid fresh random, we can specify that it \
                   hides the message.
                   Encryption at toplevel are replaced by the length of the \
                   plaintext. Encryption not at toplevel are replaced by the \
                   encryption of the length of the plaintexts."
   ~tactic_group:Cryptographic
   (only_equiv_typed cca1) Args.Int

(*------------------------------------------------------------------*)
(** Encryption key privacy  *)

let enckp
  Args.(Pair (Int i, Pair (Opt (Message, m1), Opt (Message, m2))))
  s =
  let before, e, after = split_equiv_goal i s in
  
  let biframe = List.rev_append before after in
  let cntxt = ES.mk_trace_cntxt s in
  let table = cntxt.table in
  let env = ES.env s in

  (* Apply tactic to replace key(s) in [enc] using [new_key].
   * Precondition:
   * [enc = Term.Fun ((fnenc,indices), [m; Term.Name r; k])].
   * Verify that the encryption primitive is used correctly,
   * that the randomness is fresh and that the keys satisfy their SSC. *)
  let apply
      ~(enc     : Term.message)
      ~(new_key : Term.message option)
      ~(fnenc   : Term.fname)
      ~(indices : 'a) 
      ~(m       : 'b)
      ~(r       : Term.nsymb)
      ~(k       : Term.message)
    : Goal.t list =

    let k = Term.head_normal_biterm k in
    (* Verify that key is well-formed, depending on whether the encryption is
     * symmetric or not. Return the secret key and appropriate SSC. *)
    let ssc, wrap_pk, sk =
      if Symbols.is_ftype fnenc Symbols.SEnc table then
        match Symbols.Function.get_data fnenc table with
        | Symbols.AssociatedFunctions [fndec] ->
          (fun (sk,system) ->
             let cntxt = Constr.{ cntxt with system } in
             Cca.symenc_key_ssc
               ~cntxt fnenc fndec
               ~elems:(ES.goal_as_equiv s) sk.Term.s_symb;
             Cca.symenc_rnd_ssc ~cntxt env fnenc sk biframe;
             ()
          ),
          (fun x -> x),
          k
        | _ -> assert false

      else
        match Symbols.Function.get_data fnenc table with
        | Symbols.AssociatedFunctions [fndec;fnpk] ->
          (fun (sk,system) ->
             let cntxt = Constr.{ cntxt with system } in
             Euf.key_ssc ~cntxt ~elems:(ES.goal_as_equiv s)
               ~allow_functions:(fun x -> x = fnpk) fndec sk.s_symb),
          (fun x -> Term.mk_fun table fnpk indices [x]),
          begin match k with
            | Term.Fun ((fnpk',indices'), _, [sk])
              when fnpk = fnpk' && indices = indices' -> sk
            | Term.Fun ((fnpk',indices'), _, [sk])
              when fnpk = fnpk' && indices = indices' -> sk
            | _ ->
              soft_failure
                (Tactics.Failure
                   "The first encryption is not used \
                    with the correct public key function")
          end
        | _ -> assert false

    in
    let project = function
      | Term.Name n -> n,n
      | Term.(Diff (Name l, Name r)) -> l,r
      | _ -> soft_failure (Tactics.Failure "Secret keys must be names")
    in

    let skl, skr = project sk in
    let (new_skl, new_skr), new_key =
      match new_key with
      | Some k -> project k, k
      | None -> (skl, skl), Term.Name skl
    in

    LT.check_ty_eq (Term.ty new_key) (Term.ty sk);

    (* Verify all side conditions, and create the reachability goal
     * for the freshness of [r]. *)
    let random_fresh_cond =
      try
        (* For each key we actually only need to verify the SSC
         * wrt. the appropriate projection of the system. *)
        let sysl = SystemExpr.(project_system PLeft cntxt.system) in
        let sysr = SystemExpr.(project_system PRight cntxt.system) in
        List.iter ssc
          (List.sort_uniq Stdlib.compare
             [(skl, sysl); (skr, sysr); (new_skl, sysl); (new_skr, sysr)]) ;
        let context =
          Equiv.subst_equiv [Term.ESubst (enc,Term.empty)] [e]
        in
        fresh_cond cntxt env (Term.Name r) (context@biframe)
      with Euf.Bad_ssc -> soft_failure Tactics.Bad_SSC
    in
    let fresh_goal = ES.trace_seq_of_reach random_fresh_cond s in

    (* Equivalence goal where [enc] is modified using [new_key]. *)
    let new_enc =
      Term.mk_fun table fnenc indices [m; Term.Name r; wrap_pk new_key]
    in
    let new_elem =
      Equiv.subst_equiv [Term.ESubst (enc,new_enc)] [e]
    in
    let biframe = (List.rev_append before (new_elem @ after)) in

    [Goal.Trace fresh_goal;
     Goal.Equiv (ES.set_equiv_goal biframe s)]

  in

  let target,new_key = match m1,m2 with
    | Some (Message (m1, _)), Some (Message (m2, _)) ->
      Some m1, Some m2

    | Some (Message (m1, _)), None ->
      begin match m1 with
        | Term.Fun ((f,_),_,[_;_;_]) -> Some m1, None
        | _ -> None, Some m1
      end
    | None, None -> None, None
    | None, Some _ -> assert false
  in

  match target with
  | Some (Term.Fun ((fnenc,indices), _, [m; Term.Name r; k]) as enc) ->
    apply ~enc ~new_key ~fnenc ~indices ~m ~r ~k
  | Some _ ->
    soft_failure
      (Tactics.Failure ("Target must be of the form enc(_,r,_) where \
                         r is a name"))
  | None ->
    let encs =
      Iter.get_ftypes ~excludesymtype:Symbols.ADec table Symbols.AEnc e @
      Iter.get_ftypes ~excludesymtype:Symbols.SDec table Symbols.SEnc e
    in
    (** Run [apply] on first item in [encs] that is well-formed
      * and has a diff in its key.
      * We could also backtrack in case of failure. *)
    let diff_key = function
      | Term.Diff _ | Term.Fun (_, _, [Term.Diff _]) -> true
      | _ -> false
    in

    let rec find = function
      | occ :: occs ->
        if not (Sv.is_empty occ.Iter.occ_vars) then find occs 
        else 
        begin match occ.Iter.occ_cnt with
          | Term.Fun ((fnenc,indices), _, [m; Term.Name r; k]) as enc 
            when diff_key k ->
            apply ~enc ~new_key ~fnenc ~indices ~m ~r ~k
      
          | _ -> find occs
        end
      
      | [] ->
        soft_failure
          (Tactics.Failure ("no subterm of the form enc(_,r,k) where \
                             r is a name and k contains a diff(_,_)"))
    in find encs

let () =
  T.register_typed "enckp"
    ~general_help:"Change the key in some encryption subterm."
    ~detailed_help:"This captures the fact that an encryption key may hide the \
                    key.  The term and new key can be passed as arguments, \
                    otherwise the tactic applies to the first subterm of the form \
                    enc(_,r,k) where r is a name and k features a diff operator."
    ~tactic_group:Cryptographic
    (only_equiv_typed enckp)
    Args.(Pair (Int, Pair (Opt Message,Opt Message)))

(*------------------------------------------------------------------*)
(** XOR *)

exception Not_xor

(* Removes the first occurence of Name (n,is) in the list l. *)
let rec remove_name_occ ns l = match l with
  | [Term.Name ns'; t] when ns = ns' -> t
  | [t; Term.Name ns'] when ns = ns' -> t
  | _ ->
    Tactics.(soft_failure (Failure "name is not XORed on both sides"))

let mk_xor_if_term_base (cntxt : Constr.trace_cntxt) env biframe
    (n_left, l_left, n_right, l_right, term) =
  let biframe =
    (Term.Diff (l_left, l_right)) :: biframe
  in

  let system_left = SystemExpr.(project_system PLeft cntxt.system) in
  let cntxt_left = { cntxt with system = system_left } in
  let phi_left = mk_phi_proj cntxt_left env n_left PLeft biframe in

  let system_right = SystemExpr.(project_system PRight cntxt.system) in
  let cntxt_right = { cntxt with system = system_right } in
  let phi_right = mk_phi_proj cntxt_right env n_right PRight biframe in

  let len_left =
    Term.(Atom (`Message (`Eq,
                          mk_len l_left,
                          mk_len (Name n_left)))) in

  let len_right =
    Term.(Atom (`Message (`Eq,
                          mk_len l_right,
                          mk_len (Name n_right)))) in

  let len = if len_left = len_right then [len_left] else [len_left;len_right] in

  let phi =
    Term.mk_ands
      (* remove duplicates, and then concatenate *)
      (len @
       List.filter (fun x -> not (List.mem x phi_right)) phi_left @
       phi_right)
  in

  let then_branch = Term.mk_zero in
  let else_branch = term in
  Term.mk_ite phi then_branch else_branch

let mk_xor_if_term cntxt env t biframe =
  let (n_left, l_left, n_right, l_right, term) =
    match Term.pi_term PLeft t, Term.pi_term PRight t with
    | (Fun (fl, _, [Term.Name nl;ll]),
       Fun (fr, _, [Term.Name nr;lr]))
      when (fl = Term.f_xor && fr = Term.f_xor) ->
      (nl,ll,nr,lr,t)

    | _ -> raise Not_xor
  in

  mk_xor_if_term_base cntxt env biframe (n_left, l_left, n_right, l_right, term)


let mk_xor_if_term_name cntxt env t mess_name biframe =
  let n_left, l_left, n_right, l_right, term =
    match Term.pi_term PLeft mess_name, Term.pi_term PRight mess_name with
    | Name nl, Name nr ->
      begin match Term.pi_term PLeft t, Term.pi_term PRight t with
        | (Fun (fl,_,ll),Fun (fr,_,lr))
          when (fl = Term.f_xor && fr = Term.f_xor) ->
          (nl,remove_name_occ nl ll,
               nr,remove_name_occ nr lr,
           t)
        | _ -> raise Not_xor
      end

    | _ -> soft_failure (Tactics.Failure "Expected a name")
  in
  mk_xor_if_term_base cntxt env biframe (n_left, l_left, n_right, l_right, term)


let xor Args.(Pair (Int i, Opt (Message, opt_m))) s =
  let before, e, after = split_equiv_goal i s in

  (* the biframe to consider when checking the freshness *)
  let biframe = List.rev_append before after in
  let cntxt = ES.mk_trace_cntxt s in
  let env = ES.env s in
  let res =
    try
      match opt_m with
      | None -> mk_xor_if_term cntxt env e biframe
      | Some (Args.Message (m,ty)) ->
        (* for now, we only allow the xor rule on message type. *)
        LT.check_ty_eq ty Type.Message;

        mk_xor_if_term_name cntxt env e m biframe
    with Not_xor -> 
      soft_failure
        (Tactics.Failure
           "Can only apply xor tactic on terms of the form u XOR v")
  in
  let biframe = List.rev_append before (res :: after) in
  [ES.set_equiv_goal biframe s]


let () =
  T.register_typed "xor"
   ~general_help:"Removes biterm (n(i0,...,ik) XOR t) if n(i0,...,ik) is fresh."
   ~detailed_help:"This yields the same freshness condition on the name as the \
                   fresh tactic."
   ~tactic_group:Cryptographic
   (pure_equiv_typed xor) Args.(Pair (Int, Opt Message))


(*------------------------------------------------------------------*)
exception Not_context

class ddh_context ~(cntxt:Constr.trace_cntxt) ~gen ~exp exact a b c
  = object (self)

 inherit Iter.iter_approx_macros ~exact ~cntxt as super

  method visit_macro ms a =
    match Symbols.Macro.get_def ms.s_symb cntxt.table with
      | Symbols.(Input | Output | State _ | Cond | Exec | Frame) -> ()
      | _ -> super#visit_macro ms a

  (* we check if the only diff are over g^ab and g^c, and that a, b and c
     appears only as g^a, g^b and g^c. *)
  method visit_message t =
    match t with
    (* any name n can occur as g^n *)
    | Term.Fun (f, _, [g1; Name n]) when f = exp && g1 = gen -> ()

    (* any names a b can occur as g^a^b *)
    | Term.(Diff(Term.(Fun (f1,_, [(Fun (f2,_, [g1; Name n1]));
                                   Name n2])),
                 Term.Fun (f, _, [g3; Name n3])))
      when f1 = exp && f2 = exp && g1 = gen && g3 = gen && n3.s_symb = c &&
           ((n1.s_symb = a && n2.s_symb = b) ||
            (n1.s_symb = b && n2.s_symb = a)) -> ()

    (* if a name a, b, c appear anywhere else, fail *)
    | Term.Name n when List.mem n.s_symb [a; b; c] -> raise Not_context

    (* if a diff is not over a valid ddh diff, we fail  *)
    | Term.Diff _ -> raise Not_context

    | _ -> super#visit_message t

end

exception Macro_found

class find_macros ~(cntxt:Constr.trace_cntxt) exact = object (self)
 inherit Iter.iter_approx_macros ~exact ~cntxt as super

  method visit_macro ms a =
    match Symbols.Macro.get_def ms.s_symb cntxt.table with
    | Symbols.(Input | Output | State _ | Cond | Exec | Frame) ->
      raise Macro_found
    | _ -> self#visit_macro ms a
end


(** If all the terms of a system can be seen as a context of the terms, where
   all the names appearing inside the terms are only used inside those, returns
   true. *)
let is_ddh_context (cntxt : Constr.trace_cntxt) ~gen ~exp a b c elem_list =
  let a,b,c = Symbols.Name.of_lsymb a cntxt.table,
              Symbols.Name.of_lsymb b cntxt.table,
              Symbols.Name.of_lsymb c cntxt.table in
  let iter = new ddh_context ~cntxt ~gen ~exp false a b c in
  let iterfm = new find_macros ~cntxt false in
  let exists_macro =
    try List.iter iterfm#visit_message elem_list; false
    with Macro_found -> true
  in

  try
    (* we check that a b and c only occur in the correct form inside the system,
       if the elements contain some macro based on the system.*)
   if exists_macro then
    SystemExpr.iter_descrs cntxt.table cntxt.system (
      fun d ->
        iter#visit_message (snd d.condition) ;
        iter#visit_message (snd d.output) ;
        List.iter (fun (_,t) -> iter#visit_message t) d.updates;
    );
   (* we then check inside the frame *)
    List.iter iter#visit_message elem_list;
    true
  with Not_context | Fresh.Name_found -> false

let is_ddh_gen tbl gen =
  match Symbols.Function.get_def gen tbl with
  | _, Symbols.DDHgen -> true
  | _ -> false

let ddh (lgen : lsymb) (na : lsymb) (nb : lsymb) (nc : lsymb) s sk fk =
  let tbl = ES.table s in
  let gen_symb = Symbols.Function.of_lsymb lgen tbl in

  if not (is_ddh_gen tbl gen_symb) then
    soft_failure ~loc:(L.loc lgen)
      (Failure "no DDH assumption on this generator");

  let exp_symb = match Symbols.Function.get_data gen_symb tbl with
    | Symbols.AssociatedFunctions [exp] -> exp
    | _ -> assert false
  in

  let gen = Term.mk_fun tbl gen_symb [] [] in
  let exp = (exp_symb, []) in

  let cntxt = ES.mk_trace_cntxt s in
  if is_ddh_context ~gen ~exp cntxt na nb nc (ES.goal_as_equiv s)
  then sk [] fk
  else soft_failure Tactics.NotDDHContext

(* DDH is called on strings that correspond to names, put potentially without
   the correct arity. E.g, with name a(i), we need to write ddh a, .... Thus, we
   cannot use the typed registering, as a is parsed as a name identifier, which
   then does not have the correct arity. *)

let () = T.register_general "ddh"
    ~tactic_help:
      {general_help = "Closes the current system, if it is an \
                       instance of a context of ddh.";
       detailed_help = "It must be called on (generator, a, b, c) where \
                        (a,b,c) are strings that corresponds \
                        to names, but without any indices. It then \
                        applies ddh to all the copies of the names, \
                        and checks that all actions of the protocol \
                        uses the names in a correct way. Can be used \
                        in collaboration with some transitivity to \
                        obtain a system where ddh can be applied.";
                  usages_sorts = [Sort (Pair (String, Pair (String, Pair( String, String))))];
                  tactic_group = Cryptographic}
    (function
       | [Args.String_name gen;
          Args.String_name v1;
          Args.String_name v2;
          Args.String_name v3] ->
         pure_equiv (ddh gen v1 v2 v3)
       | _ -> hard_failure (Tactics.Failure "improper arguments"))
