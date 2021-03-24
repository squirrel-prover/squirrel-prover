(** All equivalence tactics.
   Tactics are organized in three classes:
    - Logical -> relies on the logical properties of the sequent.
    - Strucutral -> relies on properties of protocols, or of equality over messages,...
    - Cryptographic -> relies on a cryptographic assumptions, that must be assumed.*)

open Term

type tac = EquivSequent.t Tactics.tac

module T = Prover.EquivTactics

module Args = TacticsArgs

module L = Location

module Hyps = EquivSequent.Hyps

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
let dbg s = Printer.prt (if Config.debug_tactics () then `Dbg else `Ignore) s

(*------------------------------------------------------------------*)
let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
(** {2 Utilities} *)

exception Out_of_range

(** When [0 <= i < List.length l], [nth i l] returns [before,e,after]
  * such that [List.rev_append before (e::after) = l] and
  * [List.length before = i].
  * @raise Out_of_range when [i] is out of range. *)
let nth i l =
  let rec aux i acc = function
    | [] -> raise Out_of_range
    | e::tl -> if i=0 then acc,e,tl else aux (i-1) (e::acc) tl
  in aux i [] l

(*------------------------------------------------------------------*)
(** {2 Logical Tactics} *)

(** Wrap a tactic expecting an equivalence goal (and returning arbitrary
  * goals) into a tactic expecting a general prover goal (which fails
  * when that goal is not an equivalence). *)
let only_equiv t (s : Prover.Goal.t) =
  match s with
  | Prover.Goal.Equiv s -> t s
  | _ -> Tactics.soft_failure (Tactics.Failure "Equivalence goal expected")

(** Wrap a tactic expecting and returning equivalence goals
  * into a general prover tactic. *)
let pure_equiv t s sk fk =
  let t' s sk fk =
    t s (fun l fk -> sk (List.map (fun s -> Prover.Goal.Equiv s) l) fk) fk
  in
  only_equiv t' s sk fk

(** As [pure_equiv], but with an extra arguments. *)
let pure_equiv_arg t a s sk fk =
  let t' s sk fk =
    t a s (fun l fk -> sk (List.map (fun s -> Prover.Goal.Equiv s) l) fk) fk
  in
  only_equiv t' s sk fk


(** Wrap a functiin expecting an equivalence goal (and returning arbitrary
  * goals) into a tactic expecting a general prover goal (which fails
  * when that goal is not an equivalence). *)
let only_equiv_typed t arg (s : Prover.Goal.t) =
  match s with
  | Prover.Goal.Equiv s -> t arg s
  | _ -> Tactics.soft_failure (Tactics.Failure "Equivalence goal expected")

(** Wrap a function expecting an argument and an equivalence goal and returning
   equivalence goals into a general prover function. *)
let pure_equiv_typed t arg s =
  let res = only_equiv_typed t arg s in
 List.map (fun s -> Prover.Goal.Equiv s) res

(*------------------------------------------------------------------*)
let goal_is_equiv s = match EquivSequent.goal s with
  | Atom (Equiv.Equiv e) -> true
  | _ -> false

let goal_as_equiv s = match EquivSequent.goal s with
  | Atom (Equiv.Equiv e) -> e
  | _ -> 
    (* Printexc.print_raw_backtrace Stdlib.stderr (Printexc.get_callstack 100);
     * Fmt.epr "@."; *)
    Tactics.soft_failure (Tactics.GoalBadShape "expected an equivalence")
      
let set_reach_goal f s = EquivSequent.set_goal s Equiv.(Atom (Reach f))

(** Build a trace sequent from an equivalent sequent when its conclusion is a
    [Reach _]. *)
let trace_seq_of_equiv_seq ?goal s = 
  let env    = EquivSequent.env s in
  let system = EquivSequent.system s in
  let table  = EquivSequent.table s in

  let goal = match goal, EquivSequent.goal s with
    | Some g, _ -> g
    | None, Equiv.Atom (Equiv.Reach f) -> f
    | None, _ -> 
      Tactics.soft_failure (Tactics.GoalBadShape "expected a reachability \
                                                  formulas")
  in

  let trace_s =
    TraceSequent.set_env env (TraceSequent.init ~system table goal)
  in
  
  (* We add all relevant hypotheses *)
  Hyps.fold (fun id hyp trace_s -> match hyp with
      | Equiv.Atom (Equiv.Reach h) -> 
        TraceSequent.Hyps.add (Args.Named (Ident.name id)) h trace_s
      | _ -> trace_s
    ) s trace_s 

let trace_seq_of_reach f s = trace_seq_of_equiv_seq (set_reach_goal f s)

(** Build the sequent showing that a timestamp happens. *)
let happens_premise (s : EquivSequent.t) (a : Term.timestamp) =
  let s = trace_seq_of_equiv_seq ~goal:(Term.Atom (`Happens a)) s in
  Prover.Goal.Trace s

let query_happens (s : EquivSequent.t) (a : Term.timestamp) =
  let s = trace_seq_of_equiv_seq ~goal:Term.False s in
  TraceSequent.query_happens s a

(*------------------------------------------------------------------*)
(** Admit tactic *)
let () =
  T.register_general "admit"
    ~tactic_help:{general_help = "Closes the current goal, or drop a bi-frame \
                                  element.";
                  detailed_help = "This tactic, of course, makes the proof \
                                   un-valid.";
                  usages_sorts = [Sort Args.Int];
                  tactic_group = Logical}
    (function
       | [] -> only_equiv (fun _ sk fk -> sk [] fk)
       | [TacticsArgs.Int_parsed i] ->
           pure_equiv begin fun s sk fk ->
             let before,_,after = nth i (goal_as_equiv s) in
             let s =
               EquivSequent.set_equiv_goal s (List.rev_append before after)
             in
               sk [s] fk
           end
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))


(*------------------------------------------------------------------*)
exception NoReflMacros

class exist_macros ~(system:SystemExpr.system_expr) table = object (self)
  inherit Iter.iter ~system table as super
  method visit_message t = match t with
    | Term.Macro _ -> raise NoReflMacros
    | _ -> super#visit_message t
  method visit_formula t = match t with
    | Term.Macro _ -> raise NoReflMacros
    | _ -> super#visit_formula t
end


(** Tactic that succeeds (with no new subgoal) on equivalences
  * where the two frames are identical. *)
let refl (e : Equiv.equiv) (s : EquivSequent.t) =
  let iter =
    new exist_macros ~system:(EquivSequent.system s) (EquivSequent.table s) in
  try
    (* we check that the frame does not contain macro *)
    List.iter iter#visit_term e;
    if EquivSequent.get_frame PLeft s = EquivSequent.get_frame PRight s
    then `True
    else `NoRefl
  with
  | NoReflMacros -> `NoReflMacros


(** Tactic that succeeds (with no new subgoal) on equivalences
  * where the two frames are identical. *)
let refl_tac (s : EquivSequent.t) =
  match refl (goal_as_equiv s) s with
    | `True         -> []
    | `NoRefl       -> Tactics.soft_failure (Tactics.NoRefl)
    | `NoReflMacros -> Tactics.soft_failure (Tactics.NoReflMacros)

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
(** For each element of the biframe, checks that it is a member of the
  * hypothesis biframe. If so, close the goal. *)
let assumption s =
  let goal = EquivSequent.goal s in

  let in_atom = 
    (* For equivalence goals, we look for inclusion of the goal in
       an existing equivalence hypothesis *)
    if goal_is_equiv s then
      let goal = goal_as_equiv s in
      (function
        | Equiv.Equiv equiv  -> 
          List.for_all (fun elem -> List.mem elem equiv) goal
        | Equiv.Reach _ -> false)

    else (fun at -> Equiv.Atom at = goal)
  in

  let in_hyp _ = function
    | Equiv.Atom at -> in_atom at
    | Equiv.Impl _ as f -> f = goal
  in

  if Hyps.exists in_hyp s
  then []
  else
    Tactics.soft_failure (Tactics.Failure "Conclusion different from hypothesis.")

let () =
  T.register "assumption"
    ~tactic_help:{general_help = "Closes a goal contained in its hypothesis.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    (only_equiv assumption)

(*------------------------------------------------------------------*)
(* TODO: factorize with the identical trace tactics *)
let revert (hid : Ident.t) (s : EquivSequent.t) =
  let f = Hyps.by_id hid s in
  let s = Hyps.remove hid s in
  EquivSequent.set_goal s (Equiv.Impl (f,EquivSequent.goal s))

let revert_str (Args.String hyp_name) (s : EquivSequent.t) =
  let hid,_ = Hyps.by_name hyp_name s in
  [revert hid s]

let () =
  T.register_typed "revert"
    ~general_help:"Take an hypothesis H, and turns the conclusion C into the \
                   implication H => C."
    ~detailed_help:""
    ~tactic_group:Logical
    (pure_equiv_typed revert_str) Args.String

(*------------------------------------------------------------------*)
(* TODO: factorize with corresponding, more general, trace tactics *)
let do_naming_pat (ip_handler : Args.ip_handler) nip s : EquivSequent.sequent =
  match ip_handler with
  | `Var Vars.EVar v -> 
    let env = ref (EquivSequent.env s) in

    let v' = match nip with
      | Args.Unnamed
      | Args.AnyName ->
        Vars.make_fresh_and_update env (Vars.sort v) v.Vars.name_prefix

      | Args.Named name ->
        let v' = Vars.make_fresh_and_update env (Vars.sort v) name in

        if Vars.name v' <> name then
          hard_failure (
            Tactics.Failure ("variable name " ^ name ^ " already in use"));
        v'
    in
    let subst = [Term.ESubst (Term.Var v, Term.Var v')] in

    (* FIXME: we substitute everywhere. This is inefficient. *)
    EquivSequent.subst subst (EquivSequent.set_env !env s)

  | `Hyp hid ->
    let f = Hyps.by_id hid s in
    let s = Hyps.remove hid s in

    Hyps.add nip f s

(*------------------------------------------------------------------*)
(* TODO: factorize with corresponding, more general, trace tactics *)
let do_and_pat (hid : Ident.t) s : Args.ip_handler list * EquivSequent.sequent =
  soft_failure (Tactics.Failure ("cannot destruct " ^ Ident.name hid))

(* TODO: factorize with corresponding, more general, trace tactics *)
let rec do_and_or_pat (hid : Ident.t) (pat : Args.and_or_pat) s
  : EquivSequent.sequent list =
  soft_failure (Tactics.Failure ("cannot apply and_or_pat to " ^ Ident.name hid))

and do_simpl_pat (h : Args.ip_handler) (ip : Args.simpl_pat) s
  : EquivSequent.sequent list =
  match h, ip with
  | _, Args.SNamed n_ip -> [do_naming_pat h n_ip s]

  | `Var _, Args.SAndOr ao_ip ->
    hard_failure (Tactics.Failure "intro pattern not applicable")

  | `Hyp id, Args.SAndOr ao_ip ->
    do_and_or_pat id ao_ip s

(*------------------------------------------------------------------*)
(* TODO: factorize with corresponding, more general, trace tactics *)
let rec do_intro (s : EquivSequent.t) : Args.ip_handler * EquivSequent.sequent =
  match EquivSequent.goal s with
  (* | ForAll ((Vars.EVar x) :: vs,f) ->
   *   let x' = Vars.make_new_from x in
   * 
   *   let subst = [Term.ESubst (Term.Var x, Term.Var x')] in
   * 
   *   let f = match vs with
   *     | [] -> f
   *     | _ -> ForAll (vs,f) in
   * 
   *   let new_formula = Term.subst subst f in
   *   ( `Var (Vars.EVar x'),
   *     EquivSequent.set_goal new_formula s )
   * 
   * | ForAll ([],f) ->
   *   (* FIXME: this case should never happen. *)
   *   do_intro (EquivSequent.set_goal f s) *)

  | Equiv.Impl(lhs,rhs)->
    let id, s = Hyps.add_i Args.Unnamed lhs s in
    let s = EquivSequent.set_goal s rhs in
    ( `Hyp id, s )

  (* | Not f ->
   *   let id, s = Hyps.add_i Args.Unnamed f s in
   *   let s = EquivSequent.set_goal False s in
   *   ( `Hyp id, s ) *)

  | _ -> soft_failure Tactics.NothingToIntroduce

(* TODO: factorize with corresponding, more general, trace tactics *)
let do_intro_pat (ip : Args.simpl_pat) s : EquivSequent.sequent list =
  let handler, s = do_intro s in
  do_simpl_pat handler ip s

(* TODO: factorize with corresponding, more general, trace tactics *)
let rec intro_all (s : EquivSequent.t) : EquivSequent.t list =
  try
    let s_ip = Args.(SNamed AnyName) in
    let ss = do_intro_pat s_ip s in
    List.concat_map intro_all ss
      
  with Tactics.Tactic_soft_failure (_,NothingToIntroduce) -> [s]

(* TODO: factorize with corresponding, more general, trace tactics *)
let rec do_intros (intros : Args.intro_pattern list) s =
  match intros with
  | [] -> [s]

  | Args.Tryauto l :: intros 
  | Args.Simplify l :: intros ->
    (* TODO: implement after code factorization *)
    hard_failure (Failure "not yet implemented for equiv sequents")

  | (Args.Simpl s_ip) :: intros ->
    let ss = do_intro_pat s_ip s in
    List.map (do_intros intros) ss
    |> List.flatten

  | (Args.Star loc) :: intros ->
    try
      let s_ip = Args.(SNamed AnyName) in
      let ss = do_intro_pat s_ip s in
      List.map (do_intros [Args.Star loc]) ss
      |> List.flatten

    with Tactics.Tactic_soft_failure (_,NothingToIntroduce) -> [s]

(** Correponds to `intro *`, to use in automated tactics. *)
let intro_all (s : EquivSequent.t) : EquivSequent.t list =
  let star = Args.Star L._dummy in
  do_intros [star] s

let intro_tac args s sk fk =
  try match args with
    | [Args.IntroPat intros] -> sk (do_intros intros s) fk

    | _ -> Tactics.(hard_failure (Failure "improper arguments"))
  with Tactics.Tactic_soft_failure (_,e) -> fk e

let () =
  T.register_general "intro"
    ~tactic_help:{general_help = "Introduce topmost connectives of conclusion \
                                  formula, when it can be done in an invertible, \
                                  non-branching fashion.\
                                  \n\nUsage: intro a b _ c *";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    (pure_equiv_arg intro_tac)


(*------------------------------------------------------------------*)
(** [tautology f s] tries to prove that [f] is always true in [s]. *)
let rec tautology f s = match f with
  | Equiv.Impl (f0,f1) ->
    let s = Hyps.add Args.AnyName f0 s in
    tautology f1 s
  | Equiv.(Atom (Equiv e)) -> refl e s = `True
  | Equiv.(Atom (Reach _)) -> 
    let s = EquivSequent.set_goal s f in
    let trace_s = trace_seq_of_equiv_seq s in
    (* TODO: improve automation by doing more than just constraint solving ? *)
    Tactics.timeout_get (TraceTactics.constraints trace_s) 

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
(** [generalize ts s] reverts all hypotheses that talk about [ts] in [s],
    by introducing them in the goal.
    Also returns a function that introduce back the generalized hypothesis.*)
let generalize (ts : timestamp) s =
  let ts = match ts with
    | Var t -> (Vars.EVar t) 
    | _ -> hard_failure (Failure "timestamp is not a var") in

  let gen_hyps = Hyps.fold (fun id f gen_hyps -> 
      if Vars.Sv.mem ts (Equiv.fv_form f) 
      then id :: gen_hyps 
      else gen_hyps
    ) s [] in
  
  (* generalized sequent *)
  let s = List.fold_left (fun s id -> revert id s) s gen_hyps in

  (* function introducing back generalized hypotheses *)
  let intro_back s =
    let ips = List.rev_map (fun id -> 
        let ip = Args.Named (Ident.name id) in
        Args.(Simpl (SNamed ip))
      ) gen_hyps in
    Utils.as_seq1 (do_intros ips s) in

  intro_back, s
  

(*------------------------------------------------------------------*)
(** Given a judgement [s] of the form Γ ⊢ E, and a timestamp τ, 
    produce the judgments
    Γ ⊢ E{ts → init}   and   (Γ, E{ts → pred τ}) ⊢ E.
    The second one is then direclty simplified by a case on all possible
    values of τ, producing a judgement for each one. 
    Generalizes Γ ⊢ E over τ if necessary. *)
let induction TacticsArgs.(Timestamp ts) s =
  let env = EquivSequent.env s in
  match ts with
  | Var t as ts ->
    (* Generalizes over [ts]. *)
    let intro_back, s = generalize ts s in

    (* Remove ts from the sequent, as it will become unused. *)
    let s = EquivSequent.set_env (Vars.rm_var env t) s in
    let table  = EquivSequent.table s in
    let system = EquivSequent.system s in
    let subst = [Term.ESubst (ts, Pred ts)] in
    let goal = EquivSequent.goal s in

    let ind_hyp = Equiv.subst_form subst goal in
    let id_ind, induc_s = Hyps.add_i Args.Unnamed ind_hyp s in
    (* intro back generalized hyps *)
    let induc_s = intro_back induc_s in
    (* rename the inducition hypothesis *)
    let induc_s = do_naming_pat (`Hyp id_ind) Args.AnyName induc_s in

    let init_goal = Equiv.subst_form [Term.ESubst(ts,Term.init)] goal in
    let init_s = EquivSequent.set_goal s init_goal in
    let init_s = intro_back init_s in

    let goals = ref [] in
    (** [add_action _action descr] adds to goals the goal corresponding to the
      * case where [t] is instantiated by [descr]. *)
    let add_action descr =
      if descr.Action.name = Symbols.init_action
      then ()
      else
        begin
          let env = ref @@ EquivSequent.env induc_s in
          let subst =
            List.map
              (fun i ->
                 let i' = Vars.make_fresh_from_and_update env i in
                 Term.ESubst (Term.Var i, Term.Var i'))
              descr.Action.indices
          in
          let name =
            SystemExpr.action_to_term table system
              (Action.subst_action subst descr.Action.action)
          in
          let ts_subst = [Term.ESubst(ts,name)] in
          goals := (EquivSequent.subst ts_subst induc_s
                    |> EquivSequent.set_env !env)
                   ::!goals 
        end
    in

    SystemExpr.iter_descrs table system add_action ;
    
    List.map simpl_impl (init_s :: List.rev !goals)

  | _  ->
    Tactics.soft_failure
      (Tactics.Failure "expected a timestamp variable")

let () =
  T.register_typed "induction"
    ~general_help:"Apply the induction scheme to the given timestamp."
    ~detailed_help:"Given a timestamp ts, that does not occur in the hypothesis, \
                    it creates two sub-goals, one where ts has been replaced by \
                    init, and one where we assume that the goal holds on \
                    pred(ts)."
    ~tactic_group:Logical
    (pure_equiv_typed induction) TacticsArgs.Timestamp

(*------------------------------------------------------------------*)
let enrich arg s = match arg with
  | TacticsArgs.ETerm (Sorts.Boolean, f, loc) ->
    EquivSequent.set_equiv_goal s (Equiv.Formula f :: goal_as_equiv s) 

  | TacticsArgs.ETerm (Sorts.Message, f, loc) ->
    EquivSequent.set_equiv_goal s (Equiv.Message f :: goal_as_equiv s)

  | TacticsArgs.ETerm (Sorts.Index, _, loc)
  | TacticsArgs.ETerm (Sorts.Timestamp, _, loc) ->
    Tactics.hard_failure
      (Tactics.Failure "expected a message or boolean term")

let enrich_a arg s = 
  let tbl, env = EquivSequent.table s, EquivSequent.env s in
  match TacticsArgs.convert_args tbl env [arg] Args.(Sort ETerm) with
  | Args.Arg (ETerm _ as arg) -> enrich arg s
  | _ -> Tactics.(hard_failure (Failure "improper arguments"))

let enrichs args s = 
  List.fold_left (fun s arg -> enrich_a arg s) s args

let enrich_tac args s sk fk = 
  try sk [enrichs args s] fk with
  | Tactics.Tactic_soft_failure (_,e) -> fk e

let () = 
  T.register_general "enrich"
    ~tactic_help:{
      general_help  = "Enrich the goal with the given term.";
      detailed_help = "This is usually called before the induction, to enrich the \
                       induction hypothesis, and then allow to solve multiple cases \
                       more simply.";
      tactic_group  = Logical;
      usages_sorts  = [Sort TacticsArgs.Message; Sort TacticsArgs.Boolean]; }
    (pure_equiv_arg enrich_tac)


(*------------------------------------------------------------------*)
let print_tac TacticsArgs.None s =
  Tactics.print_system (EquivSequent.table s) (EquivSequent.system s);
  [s]

let () =
  T.register_typed "print" ~general_help:"Shows the current system."
    ~detailed_help:""
    ~tactic_group:Logical
    (pure_equiv_typed print_tac) TacticsArgs.None


(*------------------------------------------------------------------*)
(** {2 Structural Tactics} *)


(*------------------------------------------------------------------*)
(** Function application *)

exception No_common_head
exception No_FA
let fa_expand t =
  let aux : type a. a Term.term -> Equiv.equiv = function
    | Fun (f,l) ->
      List.map (fun m -> Equiv.Message m) l
    | ITE (c,t,e) when t = e ->
      EquivSequent.[ Message t ]
    | ITE (c,t,e) ->
      EquivSequent.[ Formula c ; Message t ; Message e ]
    | And (f,g) ->
      EquivSequent.[ Formula f ; Formula g ]
    | Or (f,g) ->
      EquivSequent.[ Formula f ; Formula g ]
    | Atom (`Message (_,f,g)) ->
      EquivSequent.[ Message f ; Message g ]
    | Impl (f,g) ->
      EquivSequent.[ Formula f ; Formula g ]
    | Not f -> EquivSequent.[ Formula f ]
    | True -> []
    | False -> []
    | Diff _ -> raise No_common_head
    | _ -> raise No_FA
  in
  (* Remve ITE(b,true,false) coming from expansion of frame macro *)
  let filterBoolAsMsg =
    List.map
      (fun x -> match x with
        | Equiv.Message ITE (c,t,e)
          when (t = Term.Fun(f_true,[]) && e = Term.Fun(f_false,[]))
          -> Equiv.Formula c
        | _ -> x)
  in
  match t with
  | Equiv.Message e -> filterBoolAsMsg (aux (Term.head_normal_biterm e))
  | Equiv.Formula e -> filterBoolAsMsg (aux (Term.head_normal_biterm e))

let fa TacticsArgs.(Int i) s =
  match nth i (goal_as_equiv s) with
    | before, e, after ->
        begin try
          (* Special case for try find, otherwise we use fa_expand *)
          match e with
          | Equiv.Message Find (vars,c,t,e) ->
            let env = ref (EquivSequent.env s) in
            let vars' = List.map (Vars.make_fresh_from_and_update env) vars in
            let subst =
              List.map2
                (fun i i' -> ESubst (Term.Var i, Term.Var i'))
                vars vars'
            in
            let c' = Term.(Seq (vars, message_of_formula c)) in
            let t' = Term.subst subst t in
            let biframe =
              List.rev_append before
                (Equiv.[ Message c' ; Message t' ; Message e ] @ after)
            in
            [ EquivSequent.set_env !env (EquivSequent.set_equiv_goal s biframe) ]
          | _ ->
            let biframe =
              List.rev_append before (fa_expand e @ after) in
              [ EquivSequent.set_equiv_goal s biframe ]
          with
          | No_common_head ->
              Tactics.soft_failure (Tactics.Failure "No common construct")
          | No_FA ->
              Tactics.soft_failure (Tactics.Failure "FA not applicable")
        end
    | exception Out_of_range ->
        Tactics.soft_failure (Tactics.Failure "Out of range position")

let () =
  T.register_typed "fa"
    ~general_help:"Break function applications on the nth term of the sequence."
    ~detailed_help:"To prove that a goal containing f(u1,...,un) is \
                    diff-equivalent, one can prove that the goal containing the \
                    sequence u1,...,un is diff-equivalent."
    ~tactic_group:Structural
    (pure_equiv_typed fa) TacticsArgs.Int

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
      | Equiv.Message (Term.Macro (im,[],t)) when im = Term.in_macro ->
          List.exists
            (function
               | Equiv.Message (Term.Macro (fm,[],t'))
                 when fm = Term.frame_macro && leq (Pred t) t' -> true
               | _ -> false)
            elems
      | Equiv.Formula (Term.Macro (em,[],t)) when em = Term.exec_macro ->
          List.exists
            (function
               | Equiv.Message (Term.Macro (fm,[],t'))
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
  let table = EquivSequent.table s in

  (* TODO: allow to choose the hypothesis through its id *)
  let hyp = Hyps.find_map (fun _id hyp -> match hyp with
      | Equiv.(Atom (Equiv e)) -> Some e
      | _ -> None) s in

  let hyp = Utils.odflt [] hyp in

  let biframe = goal_as_equiv s
                |> List.rev
                |> filter_fa_dup table [] hyp
  in
  [EquivSequent.set_equiv_goal s biframe]

exception Not_FADUP_formula
exception Not_FADUP_iter

class check_fadup ~(system:SystemExpr.system_expr) table tau = object (self)

  inherit [Term.timestamp list] Iter.fold ~system table as super

  method check_formula f = ignore (self#fold_formula [Term.Pred tau] f)

  method extract_ts_atoms phi =
    let rec conjuncts = function
      | And (f,g) :: l -> conjuncts (f::g::l)
      | f :: l -> f :: conjuncts l
      | [] -> []
    in
    List.partition
      (function Atom (`Timestamp _) -> true | _ -> false)
      (conjuncts [phi])

  method add_atoms atoms timestamps =
    List.fold_left
      (fun acc at -> match at with
        | Atom (`Timestamp (`Leq,tau_1,tau_2)) ->
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
           (ms = Term.out_macro && List.mem a timestamps)
      -> timestamps
    | ITE (Macro (ms,[],a), then_branch, _)
      when ms = Term.exec_macro && List.mem a timestamps
      -> self#fold_message timestamps then_branch
    | Macro _ | Name _ | Var _ | Diff _ -> raise Not_FADUP_iter
    | Fun _ | Seq _ | ITE _ | Find _ -> super#fold_message timestamps t

  method fold_formula timestamps (f:Term.formula) =
    match f with
    | Atom (`Index _) | Atom (`Timestamp _) -> timestamps
    | Impl (phi_1,phi_2) ->
      let atoms,l = self#extract_ts_atoms phi_1 in
      let ts' = self#add_atoms atoms timestamps in
      List.iter
        (fun phi -> ignore (self#fold_formula ts' phi))
        (phi_2::l) ;
      timestamps
    | And _ as phi ->
      let atoms,l = self#extract_ts_atoms phi in
      let ts' = self#add_atoms atoms timestamps in
      List.iter
        (fun phi -> ignore (self#fold_formula ts' phi))
        l ;
      timestamps
    | Atom (`Happens _) | Var _ | Diff _ | Macro _ -> raise Not_FADUP_iter
    | Atom (`Message _)
    | Or _ | Not _ | ForAll _ | Exists _ -> super#fold_formula timestamps f
    | True | False -> timestamps

end

let fa_dup_int i s =
  match nth i (goal_as_equiv s) with
  | before, e, after ->
      let biframe_without_e = List.rev_append before after in
      let system = EquivSequent.system s in
      let table  = EquivSequent.table s in
      begin try
        (* we expect that e is of the form exec@pred(tau) && phi *)
        let (tau,phi) =
          let f,g = match e with
            | Equiv.Formula Term.And (f,g) -> f,g
            | Equiv.Message Term.(Seq (vars,ITE (And (f,g),tt,ff)))
              when Term.(tt = Fun (f_true,[]) && ff = Fun (f_false,[])) ->
              let subst =
                List.map
                  (fun v ->
                     ESubst (Var v, Var (Vars.make_new_from v)))
                  vars
              in
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
          Equiv.Message (Term.Macro (Term.frame_macro,[],Term.Pred tau))
        in
        (* we first check that frame@pred(tau) is in the biframe *)
        if List.mem frame_at_pred_tau biframe_without_e then
          (* we iterate over the formula phi to check if it contains only
           * allowed subterms *)
          let iter = new check_fadup ~system table tau in
          iter#check_formula phi ;
          (* on success, we keep only exec@pred(tau) *)
          let new_elem =
            Equiv.Formula
              (Term.Macro (Term.exec_macro,[],Term.Pred tau))
          in
          [EquivSequent.set_equiv_goal s (List.rev_append before (new_elem::after))]
        else raise Not_FADUP_formula
      with
      | Not_FADUP_formula ->
          Tactics.soft_failure (Tactics.Failure "can only apply the tactic on \
          a formula of the form (exec@pred(tau) && phi) with frame@pred(tau)\
          in the biframe")
      | Not_FADUP_iter ->
          Tactics.soft_failure (Tactics.Failure "the formula contains subterms \
          that are not handled by the FADUP rule")
      end
  | exception Out_of_range ->
      Tactics.soft_failure (Tactics.Failure "out of range position")


let fadup TacticsArgs.(Opt (Int, p)) s =
  match p with
  | None -> fa_dup s
  | Some (TacticsArgs.Int i) -> fa_dup_int i s

let () =
 T.register_typed "fadup"
   ~general_help:"When applied without argument, tries to remove all terms that \
                  are duplicates, or context of duplicates."
   ~detailed_help: "When applied on a formula of the form (exec@pred(tau) && \
                    phi), with frame@pred(tau) in the biframe, tries to remove \
                    phi if it contains only subterms allowed by the FA-DUP rule."
   ~tactic_group:Structural
   (pure_equiv_typed fadup) TacticsArgs.(Opt Int)

(*------------------------------------------------------------------*)
(** Fresh *)

(** Construct the formula expressing freshness for some projection. *)
let mk_phi_proj system table env name indices proj biframe =
  let proj_frame = List.map (Equiv.pi_elem proj) biframe in
  begin try
    let list_of_indices_from_frame =
      let iter = new Fresh.get_name_indices ~system table false name in
        List.iter iter#visit_term proj_frame ;
        iter#get_indices
    and list_of_actions_from_frame =
      let iter = new Fresh.get_actions ~system table false in
      List.iter iter#visit_term proj_frame ;
      iter#get_actions
    and tbl_of_action_indices = Hashtbl.create 10 in
    SystemExpr.(iter_descrs table system
      (fun action_descr ->
        let iter = new Fresh.get_name_indices ~system table true name in
        let descr_proj = Action.pi_descr proj action_descr in
        iter#visit_formula (snd descr_proj.condition) ;
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
                  (fun i -> not (Vars.mem env (Vars.name i)))
                  j
              in
              let env = ref env in
              let bv' =
                List.map (Vars.make_fresh_from_and_update env) bv in
              let subst =
                List.map2
                  (fun i i' -> ESubst (Term.Var i, Term.Var i'))
                  bv bv'
              in
              let j = List.map (Term.subst_var subst) j in
              Term.mk_forall
                (List.map (fun i -> Vars.EVar i) bv')
                (Term.mk_indices_neq indices j))
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
                (fun i -> Vars.make_fresh_from_and_update env i)
                a.Action.indices
            in
            let bv =
              List.filter
                (fun i -> not (List.mem i a.Action.indices))
                (List.sort_uniq Stdlib.compare (List.concat indices_a))
            in
            let bv' =
              List.map
                (fun i -> Vars.make_fresh_from_and_update env i)
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
              SystemExpr.action_to_term table system
                (Action.subst_action subst a.Action.action)
            in
            let indices_a =
              List.map
                (List.map (Term.subst_var subst))
                indices_a in
            (* if new_action occurs before an action of the frame *)
            let disj =
              Term.mk_ors
                (List.sort_uniq Stdlib.compare
                  (List.map
                    (fun (t,strict) ->
                      if strict
                      then Term.Atom (`Timestamp (`Lt, new_action, t))
                      else Term.Atom (Term.mk_timestamp_leq new_action t))
                    list_of_actions_from_frame))
            (* then indices of name in new_action and of [name] differ *)
            and conj =
              Term.mk_ands
                (List.map
                   (fun is -> Term.mk_indices_neq is indices)
                   indices_a)
            in
            let forall_var =
              List.map (fun i -> Vars.EVar i) (new_action_indices @ bv') in
            (Term.mk_forall forall_var (Term.mk_impl disj conj))::formulas)
        tbl_of_action_indices
        []
    in
    phi_frame @ phi_actions
  with
  | Fresh.Name_found ->
      Tactics.soft_failure (Tactics.Failure "Name not fresh")
  | Fresh.Var_found ->
      Tactics.soft_failure
        (Tactics.Failure "Variable found, unsound to apply fresh")
  end

let fresh_cond system table env t biframe =
  let (n_left, ind_left, n_right, ind_right) =
    match
      Term.pi_term PLeft t, Term.pi_term PRight t
    with
    | (Name (nl,isl), Name (nr,isr)) -> (nl,isl,nr,isr)
    | _ -> raise Fresh.Not_name
  in
  let system_left = SystemExpr.(project_system PLeft system) in
  let phi_left =
    mk_phi_proj system_left table env n_left ind_left PLeft biframe
  in
  let system_right = SystemExpr.(project_system PRight system) in
  let phi_right =
    mk_phi_proj system_right table env n_right ind_right PRight biframe
  in
  mk_ands
    (* remove duplicates, and then concatenate *)
    ((List.filter (fun x -> not(List.mem x phi_right)) phi_left)
     @
     phi_right)

(** Returns the term if (phi_left && phi_right) then 0 else diff(nL,nR). *)
let mk_if_term system table env e biframe =
  match e with
  | Equiv.Message t ->
    let phi = fresh_cond system table env t biframe in
    let then_branch = Term.Fun (Term.f_zero,[]) in
    let else_branch = t in
    Equiv.Message Term.(mk_ite phi then_branch else_branch)
  | Equiv.Formula f -> raise Fresh.Not_name

let fresh TacticsArgs.(Int i) s =
  match nth i (goal_as_equiv s) with
    | before, e, after ->
        (* the biframe to consider when checking the freshness *)
        let biframe = List.rev_append before after in
        let system = EquivSequent.system s in
        let table  = EquivSequent.table s in
        let env    = EquivSequent.env s in
        begin match mk_if_term system table env e biframe with
        | if_term ->
          let biframe = List.rev_append before (if_term::after) in
          [EquivSequent.set_equiv_goal s biframe]
        | exception Fresh.Not_name ->
          Tactics.soft_failure
            (Tactics.Failure "Can only apply fresh tactic on names")
        end
    | exception Out_of_range ->
        Tactics.soft_failure (Tactics.Failure "Out of range position")

let () =
  T.register_typed "fresh"
    ~general_help:"Removes a name if fresh."
    ~detailed_help:"This replaces a name n by the term 'if fresh(n) then zero \
                    else n, where fresh(n) captures the fact that this specific \
                    instance of the name cannot have been produced by another \
                    action.'"
    ~tactic_group:Structural
    (pure_equiv_typed fresh) TacticsArgs.Int



(*------------------------------------------------------------------*)  
(** Sequence expansion of the sequence [term] for the given parameters [ths]. *)
let expand_seq (term:Theory.term) (ths:Theory.term list) (s:EquivSequent.t) =
  let env = EquivSequent.env s in
  let table = EquivSequent.table s in
  let tsubst = Theory.subst_of_env env in
  let conv_env = Theory.{ table = table; cntxt = InGoal; } in
  match Theory.convert conv_env tsubst term Sorts.Message with
  (* we expect term to be a sequence *)
  | Seq ( vs, t) as term_seq ->
    let vs = List.map (fun x -> Vars.EVar x) vs in
    (* we parse the arguments ths, to create a substution for variables vs *)
    let subst = Theory.parse_subst table env vs ths in
    (* new_t is the term of the sequence instantiated with the subst *)
    let new_t = Equiv.Message (Term.subst subst t) in
    (* we add the new term to the frame and the hypothesis if it does not yet
       belongs to it *)
    let biframe =
      let old_biframe = goal_as_equiv s in
      if List.mem new_t old_biframe then old_biframe else new_t :: old_biframe
    in
    
    let rec mk_hyp_f = function
      | Equiv.Atom at -> 
        Equiv.Atom (mk_hyp_at at)
      | Equiv.Impl (f, f0) -> 
        Equiv.Impl (mk_hyp_f f, mk_hyp_f f0) 

    and mk_hyp_at hyp = match hyp with
      | Equiv.Equiv e ->
        let new_e = 
          if not (List.mem new_t e) && List.mem (Equiv.Message term_seq) e
          then new_t :: e
          else e 
        in
        Equiv.Equiv new_e

      | Equiv.Reach f -> hyp
    in

    let s = Hyps.map mk_hyp_f s in    

    [ EquivSequent.set_equiv_goal s biframe]
  | _ ->
    Tactics.hard_failure
      (Tactics.Failure "can only expand with sequences with parameters")

(* Expand all occurrences of the given macro [term] inside [s] *)
let expand (term : Theory.term) (s : EquivSequent.t) =
  let tsubst = Theory.subst_of_env (EquivSequent.env s) in
  (* final function once the substitution has been computed *)
  let succ a subst =
    let apply_subst = function
      | Equiv.Message e -> Equiv.Message (Term.subst subst e)
      | Equiv.Formula e -> Equiv.Formula (Term.subst subst e)
    in
    let new_s = 
      EquivSequent.set_equiv_goal s (List.map apply_subst (goal_as_equiv s)) 
    in   
    
    if not (query_happens ~precise:true s a) 
    then soft_failure (Tactics.MustHappen a)
    else [Prover.Goal.Equiv new_s]
  in

  let table = EquivSequent.table s in
  (* computes the substitution dependeing on the sort of term *)
  let conv_env = Theory.{ table = table; cntxt = InGoal; } in

  match Theory.convert conv_env tsubst term Sorts.Boolean with
    | Macro ((mn, sort, is),l,a) ->
      if Macros.is_defined mn a table then
        succ a [Term.ESubst (Macro ((mn, sort, is),l,a),
                           Macros.get_definition
                             (EquivSequent.system s) table sort mn is a)]
      else Tactics.soft_failure (Tactics.Failure "cannot expand this macro")

    | _ ->
      Tactics.soft_failure (Tactics.Failure "can only expand macros")

    | exception Theory.(Conv (_,Type_error _)) ->
      match Theory.convert conv_env tsubst term Sorts.Message with
      | Macro ((mn, sort, is),l,a) ->
        if Macros.is_defined mn a table then
          succ a [Term.ESubst (Macro ((mn, sort, is),l,a),
                             Macros.get_definition
                               (EquivSequent.system s) table sort mn is a)]
        else Tactics.soft_failure (Tactics.Failure "cannot expand this macro")
      | _ ->
        Tactics.soft_failure (Tactics.Failure "can only expand macros")

(* Does not rely on the typed registering, as it parsed a substitution. *)
let () = T.register_general "expand"

    ~tactic_help:{general_help = "Expand all occurrences of the given macro, or \
                                  expand the given sequence using the given \
                                  indices.";
                  detailed_help = "The value of the macro is obtained by looking \
                                   at the corresponding action in the \
                                   protocol. It cannot be used on macros with \
                                   unknown timestamp.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
  (function
    | [TacticsArgs.Theory v] ->
      only_equiv (fun s sk fk -> match expand v s with
          | subgoals -> sk subgoals fk
          | exception Tactics.Tactic_soft_failure (_,e) -> fk e)

    | (TacticsArgs.Theory v)::ids ->
        let ids =
          List.map (function
               | TacticsArgs.Theory th -> th
               | _ -> Tactics.hard_failure 
                        (Tactics.Failure "improper arguments")
            ) ids
        in
        pure_equiv
          (fun s sk fk -> match expand_seq v ids s with
             | subgoals -> sk subgoals fk
             | exception Tactics.Tactic_soft_failure (_,e) -> fk e)

     | _ ->
         Tactics.hard_failure
           (Tactics.Failure "improper arguments"))

(*------------------------------------------------------------------*)
(** Expands all macro occurrences inside the biframe, if the macro is not at
  * some pred(A) but about at a concrete action that is known to happen.
  * Acts recursively, also expanding the macros inside macro definition. *)
let expand_all () s =
  let expand_all_macros t system table =
    let rec aux : type a. a term -> a term = function
      | Macro ((mn, sort, is),l,a) as m
        when Macros.is_defined mn a table ->
        if query_happens ~precise:true s a 
        then aux (Macros.get_definition system table sort mn is a)
        else m
      | Macro _ as m -> m
      | Fun (f, l) -> Fun (f, List.map aux l)
      | Name n as a-> a
      | Var x as a -> a
      | Diff(a, b) -> Diff(aux a, aux b)
      | ITE (a, b, c) -> ITE(aux a, aux b, aux c)
      | Seq (a, b) -> Seq(a, aux b)
      | Find (a, b, c, d) -> Find(a, aux b, aux c, aux d)
      | And (l,r) -> And (aux l, aux r)
      | Or (l,r) -> Or (aux l, aux r)
      | Impl (l,r) -> Impl (aux l, aux r)
      | Not f -> Not (aux f)
      | True -> True
      | False -> False
      | ForAll (vs,l) -> ForAll (vs, aux l)
      | Exists (vs,l) -> Exists (vs, aux l)
      | Atom (`Message (o, t, t')) -> Atom (`Message (o, aux t, aux t'))
      | Atom (`Index _) as a-> a
      | Atom (`Timestamp _) as a->  a
      | Atom (`Happens _) as a->  a
      | Pred _ as a -> a
      | Action _ as a -> a
    in
    aux t
  in
  let system = EquivSequent.system s in
  let table  = EquivSequent.table s in
  let expand_all_macros = function
    | Equiv.Message e ->
      Equiv.Message (expand_all_macros e system table)
    | Equiv.Formula e ->
      Equiv.Formula (expand_all_macros e system table)
  in
  let biframe = goal_as_equiv s
                |> List.map (expand_all_macros)
  in
  [EquivSequent.set_equiv_goal s biframe]

let () = T.register "expandall"
    ~tactic_help:{general_help = "Expand all occurrences of macros that are \
                                  about explicit actions.";
                  detailed_help = "Calls expand on all possible macros, and acts \
                                   recursively.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
         (pure_equiv_typed expand_all ())

(*------------------------------------------------------------------*)
(** Replace all occurrences of [t1] by [t2] inside of [s],
  * and add a subgoal to prove that [t1 <=> t2]. *)
let equiv_formula f1 f2 (s : EquivSequent.t) =
  (* goal for the equivalence of t1 and t2 *)
  let f = Term.And(Term.Impl(f1, f2), Term.Impl(f2, f1)) in
  let trace_sequent = trace_seq_of_reach f s in

  let subgoals =
    [ Prover.Goal.Trace trace_sequent;
      Prover.Goal.Equiv
        (EquivSequent.subst [Term.ESubst (f1,f2)] s) ]
  in
  subgoals

(** Replace all occurrences of [m1] by [m2] inside of [s],
  * and add a subgoal to prove that [Eq(m1, m2)]. *)
let equiv_message m1 m2 (s : EquivSequent.t) =
  (* goal for the equivalence of t1 and t2 *)
  let trace_sequent =
    trace_seq_of_reach (Term.Atom (`Message (`Eq,m1,m2))) s
  in
  let subgoals =
    [ Prover.Goal.Trace trace_sequent;
      Prover.Goal.Equiv
        (EquivSequent.subst [Term.ESubst (m1,m2)] s) ]
  in
  subgoals


let equivalent arg s = match arg with
  | TacticsArgs.Pair (t1,t2) ->
    match t1, t2 with
    | TacticsArgs.ETerm (Sorts.Boolean, f1, _),
      TacticsArgs.ETerm (Sorts.Boolean, f2, _) ->
      equiv_formula f1 f2 s

    | TacticsArgs.ETerm (Sorts.Message, f1, _),
      TacticsArgs.ETerm (Sorts.Message, f2, _) ->
      equiv_message f1 f2 s

    | TacticsArgs.ETerm (_, _, _),
      TacticsArgs.ETerm (_, _, _)  ->
      (* TODO: improve error message + add locations *)
      Tactics.hard_failure
        (Tactics.Failure ("expected a pair of messages or a pair of booleans"))

let () = T.register_typed "equivalent"
    ~general_help:"Replace all occurrences of a formula by another, and ask to \
                   prove that they are equivalent."
    ~detailed_help:"This can be used on messages equality or formulas \
                    equivalence."
    ~tactic_group:Structural
    ~usages_sorts:[TacticsArgs.(Sort (Pair (Message, Message)));
                   TacticsArgs.(Sort (Pair (Boolean, Boolean)))]
    (only_equiv_typed equivalent)
    TacticsArgs.(Pair (ETerm, ETerm))


(*------------------------------------------------------------------*)
let simplify_ite b s cond positive_branch negative_branch =
  if b then
    (* replace in the biframe the ite by its positive branch *)
    (* ask to prove that the cond of the ite is True *)
    let trace_sequent = trace_seq_of_reach cond s in
    (positive_branch, trace_sequent)
  else
    (* replace in the biframe the ite by its negative branch *)
    (* ask to prove that the cond of the ite implies False *)
    let trace_sequent = trace_seq_of_reach (Term.Impl(cond,False)) s in
    (negative_branch, trace_sequent)


(** [get_ite ~system table elem] returns None if there is no ITE term in [elem],
    Some ite otherwise, where [ite] is the first ITE term encountered.
    Does not explore macros. *)
let get_ite ~system table elem =
  let iter = new Iter.get_ite_term ~system table in
  List.iter iter#visit_term [elem];
  iter#get_ite

let yes_no_if b TacticsArgs.(Int i) s =
  let system = EquivSequent.system s in
  let table = EquivSequent.table s in

  match nth i (goal_as_equiv s) with
  | before, elem, after ->
    (* search for the first occurrence of an if-then-else in [elem] *)
    begin match get_ite ~system table elem with
    | None ->
      Tactics.soft_failure
        (Tactics.Failure
          "can only be applied on a term with at least one occurrence
          of an if then else term")

    | Some (c,t,e) ->
      (* Context with bound variables (eg try find) are not (yet) supported.
       * This is detected by checking that there is no "new" variable,
       * which are used by the iterator to represent bound variables. *)
      let vars = (Term.get_vars c) @ (Term.get_vars t) @ (Term.get_vars e) in
      if List.exists Vars.(function EVar v -> is_new v) vars then
        Tactics.soft_failure (Tactics.Failure "application of this tactic \
          inside a context that bind variables is not supported")

      else
        let branch, trace_sequent =
          simplify_ite b s c t e in
        let new_elem =
          Equiv.subst_equiv
            [Term.ESubst (Term.ITE (c,t,e),branch)]
            [elem]
        in
        let biframe = List.rev_append before (new_elem @ after) in
        [ Prover.Goal.Trace trace_sequent;
          Prover.Goal.Equiv (EquivSequent.set_equiv_goal s biframe) ]
    end

  | exception Out_of_range ->
     Tactics.soft_failure (Tactics.Failure "out of range position")

let () =
 T.register_typed "noif"
   ~general_help:"Try to prove diff equivalence by proving that the condition at \
                  the i-th position implies False."
   ~detailed_help:"Replaces a proof goal with `if phi then u else v` by the \
                   goals 'phi <=> false' and the original goal now with v \
                   instead of the conditional."
   ~tactic_group:Structural
   (only_equiv_typed (yes_no_if false)) TacticsArgs.Int

let () =
 T.register_typed "yesif"
   ~general_help:"Try to prove diff equivalence by proving that the condition at \
                  the i-th position is True."
   ~detailed_help:"Replaces a proof goal with `if phi then u else v` by the \
                   goals 'phi <=> true' and the original goal now with u \
                   instead of the conditional."
   ~tactic_group:Structural
   (only_equiv_typed (yes_no_if true)) TacticsArgs.Int

(*------------------------------------------------------------------*)
exception Not_ifcond

(* Push the formula [f] in the message [term].
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
  | ITE (c,t,e) -> ITE (Term.Impl (f,c), t, e)
  (* m becomes if f then m else 0 *)
  | _ -> ITE (f, m, Term.Fun (Term.f_zero,[]))
  in
  match term with
  | Fun (f,terms) ->
    begin match j with
    | None -> Fun (f, List.map mk_ite terms)
    | Some (TacticsArgs.Int jj) ->
      if jj < List.length terms then
        Fun (f, List.mapi (fun i t -> if i=jj then mk_ite t else t) terms)
      else
        Tactics.soft_failure
          (Tactics.Failure "subterm at position j does not exists")
    end
  | Diff (a, b) ->
    begin match j with
    | None -> Diff (mk_ite a, mk_ite b)
    | Some (TacticsArgs.Int 0) -> Diff (mk_ite a, b)
    | Some (TacticsArgs.Int 1) -> Diff (a, mk_ite b)
    | _ ->  Tactics.soft_failure
              (Tactics.Failure "expected j is 0 or 1 for diff terms")
    end
  | Seq (vs, t) ->
    if not_in_f_vars vs then Seq (vs, mk_ite t)
    else raise Not_ifcond
  | Find (vs, b, t, e) ->
    if not_in_f_vars vs then Find (vs, b, mk_ite t, mk_ite e)
    else raise Not_ifcond
  | _ -> mk_ite term

let ifcond TacticsArgs.(Pair (Int i,
                              Pair (Opt (Int, j),
                                    Boolean f))) s =
  match nth i (goal_as_equiv s) with
  | before, e, after ->
    let cond, positive_branch, negative_branch =
      match e with
      | Equiv.Message ITE (c,t,e) -> (c, t, e)
      | _ ->  Tactics.soft_failure
                (Tactics.Failure "can only be applied to a conditional")
    in

    begin try
        let new_elem = Equiv.Message
            (ITE (cond, push_formula j f positive_branch, negative_branch))
        in
        let biframe = List.rev_append before (new_elem :: after) in
        let trace_sequent = 
          trace_seq_of_reach Term.(Impl(cond, f)) s 
        in

        [ Prover.Goal.Trace trace_sequent;
          Prover.Goal.Equiv (EquivSequent.set_equiv_goal s biframe) ]
      with
      | Not_ifcond ->
        Tactics.soft_failure 
          (Tactics.Failure "tactic not applicable because \
                            the formula contains variables that overlap with \
                            variables bound by \
                            a seq or a try find construct")
    end
  | exception Out_of_range ->
    Tactics.soft_failure (Tactics.Failure "out of range position")



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
   (only_equiv_typed ifcond) TacticsArgs.(Pair (Int, Pair( Opt Int, Boolean)))


(*------------------------------------------------------------------*)
(* TODO: should be a rewriting rule *)
let trivial_if (TacticsArgs.Int i) s =
  let system = EquivSequent.system s in
  let table = EquivSequent.table s in
  match nth i (goal_as_equiv s) with
  | before, elem, after ->
    (* search for the first occurrence of an if-then-else in [elem] *)
    begin match get_ite ~system table elem with
    | None ->
      Tactics.soft_failure
        (Tactics.Failure
          "can only be applied on a term with at least one occurrence \
           of an if then else term")
    | Some (c,t,e) ->
      let trace_seq = 
        trace_seq_of_reach (Term.Atom (`Message (`Eq,t,e))) s
      in
      let trace_goal  = Prover.Goal.Trace trace_seq in

      let new_elem =
        Equiv.subst_equiv
          [Term.ESubst (Term.ITE (c,t,e),t)]
          [elem]
      in
      let biframe = List.rev_append before (new_elem @ after) in
      [ trace_goal;
        Prover.Goal.Equiv (EquivSequent.set_equiv_goal s biframe) ]
    end
  | exception Out_of_range ->
     Tactics.soft_failure (Tactics.Failure "out of range position")

let () =
 T.register_typed "trivialif"
   ~general_help:"Simplify a conditional when the two branches are equal."
   ~detailed_help:""
   ~tactic_group:Structural
   (only_equiv_typed trivial_if) TacticsArgs.Int


(*------------------------------------------------------------------*)
(* allows to replace inside the positive branch of an if then else a term by
   another, if the condition implies there equality. *)
let ifeq
    TacticsArgs.(Pair (Int i, Pair (Message t1, Message t2)))
    s
  =
  match nth i (goal_as_equiv s) with
  | before, e, after ->
    let cond, positive_branch, negative_branch =
      match e with
      | Equiv.Message ITE (c,t,e) ->
        (c, t, e)
      | _ -> Tactics.soft_failure
               (Tactics.Failure "Can only be applied to a conditional.")
    in
    let new_elem =
      Equiv.Message (ITE (cond,
                          Term.subst [Term.ESubst (t1,t2)] positive_branch,
                          negative_branch))
    in
    let biframe = List.rev_append before (new_elem :: after) in

    let trace_sequent = 
      trace_seq_of_reach Term.(Impl(cond, Atom (`Message (`Eq,t1,t2)))) s
    in

    [ Prover.Goal.Trace trace_sequent;
      Prover.Goal.Equiv (EquivSequent.set_equiv_goal s biframe) ]

  | exception Out_of_range ->
     Tactics.soft_failure (Tactics.Failure "Out of range position")

let () = T.register_typed "ifeq"
    ~general_help:"If the given conditional implies the equality of the two \
                   given terms, substitute the first one by the second one \
                   inside the positive branch of the conditional."

    ~detailed_help:"This asks to prove that the equality is indeed implied by \
                    the condition, we can then replace any term by its equal \
                    term (with over-whelming probability) in the positive \
                    brannch."
    ~tactic_group:Structural
    (only_equiv_typed ifeq) TacticsArgs.(Pair (Int, Pair (Message, Message)))


(*------------------------------------------------------------------*)
(** Automatic simplification *)

let auto ~conclude ~strong s sk fk = 
  let wrap tac s sk fk = 
    try sk (tac s) fk with
    | Tactics.Tactic_soft_failure (_,e) -> fk e in

  let open Tactics in
  match s with
  | Prover.Goal.Equiv s ->
    let sk l _ = 
      if conclude && l <> [] 
      then fk GoalNotClosed
      else sk (List.map (fun s -> Prover.Goal.Equiv s) l) fk in
    let fk _ = sk [s] fk in

    let wfadup s sk fk = 
      let fk _ = sk [s] fk in
      wrap (fadup (Args.Opt (Args.Int, None))) s sk fk in

    andthen_list
      [try_tac wfadup;
       try_tac
         (andthen_list 
            [wrap (expand_all ());
             try_tac wfadup;
             orelse_list [wrap refl_tac;
                          wrap assumption]])]
      s sk fk

  | Prover.Goal.Trace t ->
    let sk l fk = sk (List.map (fun s -> Prover.Goal.Trace s) l) fk in
    TraceTactics.simplify ~close:conclude ~strong t sk fk

let tac_auto ~conclude args s sk fk =
   auto ~conclude s sk fk 


let () =
  T.register_general "auto"
    ~tactic_help:{general_help = "Automatically proves the goal.";
                  detailed_help = "Same as simpl.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural }
    (tac_auto ~conclude:true  ~strong:true)

let () =
  T.register_general "simpl"
    ~tactic_help:{general_help = "Automatically simplify the goal.";
                  detailed_help = "This tactics automatically calls fadup, \
                                   expands the macros, and closes goals using \
                                   refl or assumption.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural }
    (tac_auto ~conclude:false ~strong:true)


let () =
  T.register_general "autosimpl"
    ~tactic_help:{general_help = "Automatically simplify the goal.";
                  detailed_help = "This tactics automatically calls fadup, \
                                   expands the macros, and closes goals using \
                                   refl or assumption.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural }
    (tac_auto ~conclude:false ~strong:false)

(*------------------------------------------------------------------*)
(** {2 Cryptographic Tactics} *)

(*------------------------------------------------------------------*)
(** PRF axiom *)

exception Not_hash

let prf_param hash =
  match hash with
  | Term.Fun ((hash_fn, _), [t; Name (key_n,key_is)]) ->
      (hash_fn,t,key_n,key_is)
  | _ -> raise Not_hash

(** [occurrences_of_frame ~system table frame hash_fn key_n]
  * returns the list of pairs [is,m] such that [f(m,key_n[is])]
  * occurs in [frame]. Does not explore macros. *)
let occurrences_of_frame ~system table frame hash_fn key_n =
  let iter = new Iter.get_f_messages ~system table hash_fn key_n in
  List.iter iter#visit_term frame ;
  List.sort_uniq Stdlib.compare iter#get_occurrences

(** [occurrences_of_action_descr ~system table action_descr hash_fn key_n]
  * returns the list of pairs [is,m] such that [hash_fn(m,key_n[is])]
  * occurs in [action_descr]. *)
let occurrences_of_action_descr ~system table action_descr hash_fn key_n =
  let iter = new Iter.get_f_messages ~system table hash_fn key_n in
  iter#visit_message (snd action_descr.Action.output) ;
  List.iter (fun (_,m) -> iter#visit_message m) action_descr.Action.updates ;
  iter#visit_formula (snd action_descr.Action.condition) ;
  List.sort_uniq Stdlib.compare iter#get_occurrences

let mk_prf_phi_proj proj system table env biframe e hash =
  begin try
      let system = SystemExpr.(project_system proj system) in
      let (hash_fn,t,key_n,key_is) = prf_param (Term.pi_term proj hash) in
      (* create the frame on which we will iterate to compute phi_proj
         - e_without_hash is the context where all occurrences of [hash] have
            been replaced by zero
         - we also add the hashed message [t] *)
      let e_without_hash =
        Equiv.subst_equiv
          [Term.ESubst (hash,Term.Fun (Term.f_zero,[]))]
          [e]
      in

      let frame =
        (Equiv.Message t) ::
        (List.map (Equiv.pi_elem proj) (e_without_hash @ biframe)) in

      (* check syntactic side condition *)
      Euf.key_ssc
        ~elems:frame ~allow_functions:(fun x -> false)
        ~system ~table hash_fn key_n;

      (* we compute the list of hashes from the frame *)
      let list_of_hashes_from_frame =
        occurrences_of_frame ~system table frame hash_fn key_n
      and list_of_actions_from_frame =
        let iter = new Fresh.get_actions ~system table false in
        List.iter iter#visit_term frame ;
        iter#get_actions
      and tbl_of_action_hashes = Hashtbl.create 10 in

      (* we iterate over all the actions of the (single) system *)
      SystemExpr.(iter_descrs table system (fun action_descr ->
          (* we add only actions in which a hash occurs *)
          let descr_proj = Action.pi_descr proj action_descr in
          let action_hashes =
            occurrences_of_action_descr ~system table descr_proj hash_fn key_n in
          if List.length action_hashes > 0 then
            Hashtbl.add tbl_of_action_hashes descr_proj action_hashes));

      (* direct cases (for explicit occurences of hashes in the frame) *)
      let phi_frame =
        (List.map (fun (is,m) ->
             (* select bound variables in key indices [is] and in message [m]
                to quantify universally over them *)
             let env = ref env in
             let vars = Term.get_vars m in
             (* we add variables from [is] while preserving unique occurrences *)
             let vars = List.fold_left (fun vars i ->
                 if List.mem (Vars.EVar i) vars
                 then vars
                 else Vars.EVar i :: vars)
                 vars
                 is
             in

             (* we remove from [vars] free variables, ie already in [env] *)
             let not_in_env  = function
               | Vars.EVar ({Vars.var_type=Sorts.Index} as i) ->
                 not (Vars.mem !env (Vars.name i))
               | _ -> true
             in

             let vars = List.filter not_in_env vars in
             let subst =
               List.map
                 (function Vars.EVar v ->
                    Term.(ESubst (Var v,
                                  Var (Vars.make_fresh_from_and_update env v))))
                 vars
             in

             let forall_vars =
               List.map
                 (function Vars.EVar v ->
                    Vars.EVar (Term.subst_var subst v))
                 vars
             in

             let is = List.map (Term.subst_var subst) is in
             let m = Term.subst subst m in
             Term.mk_forall
               forall_vars
               (Term.mk_impl
                  (Term.mk_indices_eq key_is is)
                  (Term.Atom (`Message (`Neq, t, m)))))
            list_of_hashes_from_frame)

      (* undirect cases (for occurences of hashes in actions of the system) *)
      and phi_actions =
        Hashtbl.fold
          (fun a list_of_is_m formulas ->
             (* for each action in which a hash occurs *)
             let env = ref env in
             let new_action_indices =
               List.map
                 (fun i -> Vars.make_fresh_from_and_update env i)
                 a.Action.indices
             in

             let is =
               List.sort_uniq Stdlib.compare
                 (List.concat (List.map fst list_of_is_m))
             in

             let vars = List.sort_uniq Stdlib.compare
                 (List.concat
                    (List.map
                       (fun (_,m) -> Term.get_vars m)
                       list_of_is_m))
             in
             (* we add variables from [is] while preserving unique occurrences *)
             let vars =
               List.fold_left
                 (fun vars i ->
                    if List.mem (Vars.EVar i) vars
                    then vars
                    else Vars.EVar i :: vars)
                 vars
                 is
             in

             (* we remove from [vars] free variables,
              * ie already in [a.Action.indices] *)
             let not_in_action_indices  = function
               | Vars.EVar ({Vars.var_type=Sorts.Index} as i) ->
                 not (List.mem i a.Action.indices)
               | _ -> true
             in

             let vars = List.filter not_in_action_indices vars in
             let subst =
               List.map2
                 (fun i i' -> Term.ESubst (Term.Var i, Term.Var i'))
                 a.Action.indices new_action_indices
               @
               List.map
                 (function Vars.EVar v ->
                    Term.(ESubst (Var v,
                                  Var (Vars.make_fresh_from_and_update env v))))
                 vars
             in

             let forall_vars =
               List.map (fun i -> Vars.EVar i) new_action_indices
               @
               List.map
                 (function Vars.EVar v ->
                    Vars.EVar (Term.subst_var subst v))
                 vars
             in

             (* apply [subst] to the action and to the list of
              * key indices with the hashed messages *)
             let new_action =
               SystemExpr.action_to_term
                 table system
                 (Action.subst_action subst a.Action.action)
             in
             let list_of_is_m =
               List.map
                 (fun (is,m) ->
                    (List.map (Term.subst_var subst) is,Term.subst subst m))
                 list_of_is_m in

             (* if new_action occurs before an action of the frame *)
             let disj =
               Term.mk_ors
                 (List.sort_uniq Stdlib.compare
                    (List.map
                       (fun (t,strict) ->
                          if strict
                          then Term.Atom (`Timestamp (`Lt, new_action, t))
                          else Term.Atom (Term.mk_timestamp_leq new_action t))
                       list_of_actions_from_frame))

             (* then if key indices are equal then hashed messages differ *)
             and conj =
               Term.mk_ands
                 (List.map
                    (fun (is,m) -> Term.mk_impl
                        (Term.mk_indices_eq key_is is)
                        (Term.Atom (`Message (`Neq, t, m))))
                    list_of_is_m)
             in

             (Term.mk_forall forall_vars (Term.mk_impl disj conj))::formulas)
          tbl_of_action_hashes
          []
      in
      mk_ands (phi_frame @ phi_actions)

    with
    | Not_hash -> Term.True
    | Euf.Bad_ssc -> 
      Tactics.soft_failure (Tactics.Failure "Key syntactic side condition \
                                             not checked")
  end

(* from two conjonction formula p and q, produce its minimal diff(p, q), of the
   form (p inter q) && diff (p minus q, q minus p) *)
let combine_conj_formulas p q =
  let rec to_list = function
    | True  -> []
    | Term.And (a, b) -> to_list a @ to_list b
    | a -> [a]
  in
  (* we turn the conjonctions into list *)
  let p, q= to_list p, to_list q in
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
    (mk_ands common)
    (Term.head_normal_biterm (Term.Diff(mk_ands new_p, mk_ands !aux_q)))

let prf TacticsArgs.(Int i) s =
  match nth i (goal_as_equiv s) with
  | before, e, after ->
    let biframe = List.rev_append before after in
    let system = (EquivSequent.system s) in
    let table = EquivSequent.table s in
    let env = EquivSequent.env s in
    let e = match e with
      | Equiv.Message m ->
        Equiv.Message (Term.head_normal_biterm m)
      | Equiv.Formula f ->
        Equiv.Formula (Term.head_normal_biterm f)
    in
    (* search for the first occurrence of a hash in [e] *)
    begin match Iter.get_ftype ~system table e Symbols.Hash with
      | None ->
        Tactics.soft_failure
          (Tactics.Failure
             "PRF can only be applied on a term with at least one occurrence \
              of a hash term h(t,k)")
      | Some ((Term.Fun ((fn,_), [m; key])) as hash) ->
        (* Context with bound variables (eg try find) are not (yet) supported.
         * This is detected by checking that there is no "new" variable,
         * which are used by the iterator to represent bound variables. *)
        let vars = Term.get_vars hash in
        if List.exists Vars.(function EVar v -> is_new v) vars then
          Tactics.soft_failure (Tactics.Failure "Application of this tactic \
                                                 inside a context that bind variables is not supported")
        else
          let phi_left =
            mk_prf_phi_proj PLeft system table env biframe e hash in
          let phi_right =
            mk_prf_phi_proj PRight system table env biframe e hash in

          let table,n = 
            Symbols.Name.declare table (L.mk_loc L._dummy "n_PRF") 0 
          in
          let s = EquivSequent.set_table s table in

          let oracle_formula =
            Prover.get_oracle_tag_formula (Symbols.to_string fn)
          in

          let final_if_formula = match oracle_formula with
            | Term.False -> combine_conj_formulas phi_left phi_right
            | f ->
              let (Vars.EVar uvarm),(Vars.EVar uvarkey),f = match f with
                | ForAll ([uvarm;uvarkey],f) -> uvarm,uvarkey,f
                | _ -> assert false
              in
              match Vars.sort uvarm,Vars.sort uvarkey with
              | Sorts.(Message, Message) -> let f = Term.subst [
                  ESubst (Term.Var uvarm,m);
                  ESubst (Term.Var uvarkey,key);] f in
                Term.And (Term.Not f,  
                          combine_conj_formulas phi_left phi_right)
              | _ -> assert false
          in

          let if_term =
            Term.ITE
              (final_if_formula,
               Term.Name (n,[]),
               hash) in
          let new_elem =
            Equiv.subst_equiv [Term.ESubst (hash,if_term)] [e] in
          let biframe = (List.rev_append before (new_elem @ after)) in
          [EquivSequent.set_equiv_goal s biframe]
      | _ -> assert false
    end
  | exception Out_of_range ->
    Tactics.soft_failure (Tactics.Failure "Out of range position")

let () =
  T.register_typed "prf"
    ~general_help:"Apply the PRF axiom."
    ~detailed_help:"It allows to replace a hash h(m) by 'if new_hash(m) then \
                    zero else h(m)' where new_hash(m) expresses the fact that m \
                    was never hashed before. Its behaviour is simalar to the \
                    fresh tactic."
    ~tactic_group:Cryptographic
    (pure_equiv_typed prf) TacticsArgs.Int

(*------------------------------------------------------------------*)
(** Symmetric encryption **)


(** CCA1 *)

let cca1 TacticsArgs.(Int i) s =
  match nth i (goal_as_equiv s) with
  | before, e, after ->
    let biframe = List.rev_append before after in
    let system = (EquivSequent.system s) in
    let table = EquivSequent.table s in
    let env = EquivSequent.env s in
    let e = match e with
      | Equiv.Message m ->
        Equiv.Message (Term.head_normal_biterm m)
      | Equiv.Formula f ->
        Equiv.Formula (Term.head_normal_biterm f)
    in
    let get_subst_hide_enc enc fnenc m fnpk sk fndec r eis isk is_top_level =
      (* we check that the random is fresh, and the key satisfy the
               side condition. *)
      begin

        (* we create the fresh cond reachability goal *)
        let random_fresh_cond = 
          fresh_cond system table env (Term.Name r) biframe 
        in

        let fresh_seq = trace_seq_of_reach random_fresh_cond s in
        let fresh_goal = Prover.Goal.Trace fresh_seq in

        let new_subst =
          if  is_top_level then
            Term.ESubst (enc, Term.Fun (Term.f_len, [m]))
          else
            let new_m = Term.(Fun (f_zeroes, [Fun (f_len, [m])])) in
            let new_term = match fnpk with
              | Some fnpk ->     Term.Fun ((fnenc,eis),
                                           [new_m; Term.Name r;
                                            Term.Fun (fnpk, [Term.Name (sk,isk)])])
              | None ->  Term.Fun ((fnenc,eis),
                                   [new_m; Term.Name r; Term.Name (sk,isk)])
            in
            Term.ESubst (enc,
                         new_term
                        ) in
        (fresh_goal, new_subst)
      end
    in

    (* first, we check if the term is an encryption at top level, in which case
       we will completely replace the encryption by the length, else we will
       replace the plain text by the lenght *)
    let is_top_level = match e with
      | Equiv.Message (Term.Fun ((fnenc,eis), [m; Term.Name r;
                                               Term.Fun ((fnpk,is), [Term.Name (sk,isk)])]))
        when (Symbols.is_ftype fnpk Symbols.PublicKey table
              && Symbols.is_ftype fnenc Symbols.AEnc table) -> true
      | Equiv.Message (Term.Fun ((fnenc,eis), [m; Term.Name r; Term.Name (sk,isk)]))
        when Symbols.is_ftype fnenc Symbols.SEnc table -> true
      | _ -> false
    in
    (* search for the first occurrence of an asymmetric encryption in [e], that
       do not occur under a decryption symbol. *)
    let rec hide_all_encs enclist =
      begin match
          enclist
        with
        | (Term.Fun ((fnenc,eis), [m; Term.Name r;
                                   Term.Fun ((fnpk,is), [Term.Name (sk,isk)])])
           as enc) :: q when (Symbols.is_ftype fnpk Symbols.PublicKey table
                              && Symbols.is_ftype fnenc Symbols.AEnc table)
          ->
          begin
            match Symbols.Function.get_data fnenc table with
            (* we check that the encryption function is used with the associated
               public key *)
            | Symbols.AssociatedFunctions [fndec; fnpk2] when fnpk2 = fnpk
              ->
              begin
                try
                  Euf.key_ssc ~messages:[enc] ~allow_functions:(fun x -> x = fnpk)
                    ~system ~table fndec sk;
                  if not (List.mem (Equiv.Message
                                      (Term.Fun ((fnpk,is), [Term.Name (sk,isk)]))
                                   ) biframe) then
                    Tactics.soft_failure
                      (Tactics.Failure
                         "The public key must be inside the frame in order to \
                          use CCA1")
                  ;
                  let (fgoals, substs) = hide_all_encs q in
                  let fgoal,subst =
                    get_subst_hide_enc enc fnenc m (Some (fnpk,is)) sk fndec r eis isk is_top_level
                  in
                  (fgoal :: fgoals,subst :: substs)
                with Euf.Bad_ssc ->  Tactics.soft_failure Tactics.Bad_SSC
              end
            | _ ->
              Tactics.soft_failure
                (Tactics.Failure
                   "The first encryption symbol is not used with the correct \
                    public key function.")
          end

        | (Term.Fun ((fnenc,eis), [m; Term.Name r; Term.Name (sk,isk)])
           as enc) :: q when Symbols.is_ftype fnenc Symbols.SEnc table
          ->
          begin
            match Symbols.Function.get_data fnenc table with
            (* we check that the encryption function is used with the associated
               public key *)
            | Symbols.AssociatedFunctions [fndec]
              ->
              begin
                try
                  Cca.symenc_key_ssc  ~elems:(goal_as_equiv s) ~messages:[enc]
                    ~system table fnenc fndec sk;
                  (* we check that the randomness is ok in the system and the
                     biframe, except for the encryptions we are looking at, which
                     is checked by adding a fresh reachability goal. *)
                  Cca.symenc_rnd_ssc ~system table env fnenc sk isk biframe;
                  let (fgoals, substs) = hide_all_encs q in
                  let fgoal,subst =
                    get_subst_hide_enc enc fnenc m (None) sk fndec r eis isk is_top_level
                  in
                  (fgoal :: fgoals,subst :: substs)
                with Euf.Bad_ssc ->  Tactics.soft_failure Tactics.Bad_SSC
              end
            | _ ->
              Tactics.soft_failure
                (Tactics.Failure
                   "The first encryption symbol is not used with the correct public \
                    key function.")
          end
        | [] -> [], []
        | _ ->
          Tactics.soft_failure
            (Tactics.Failure
               "CCA1 can only be applied on a term with at least one occurrence \
                of an encryption term enc(t,r,pk(k))")
      end
    in
    let fgoals, substs = hide_all_encs ((Iter.get_ftypes ~excludesymtype:Symbols.ADec
                                           ~system table e Symbols.AEnc)
                                        @ (Iter.get_ftypes ~excludesymtype:Symbols.SDec
                                             ~system table e Symbols.SEnc)) in
    if substs = [] then
      Tactics.soft_failure
        (Tactics.Failure
           "CCA1 can only be applied on a term with at least one occurrence \
            of an encryption term enc(t,r,pk(k))");
    let new_elem =    Equiv.subst_equiv substs [e] in
    let biframe = (List.rev_append before (new_elem @ after)) in
    Prover.Goal.Equiv (EquivSequent.set_equiv_goal s biframe) :: fgoals

  | exception Out_of_range ->
    Tactics.soft_failure (Tactics.Failure "Out of range position")


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
   (only_equiv_typed cca1) TacticsArgs.Int

(*------------------------------------------------------------------*)
(** Encryption key privacy  *)

let enckp
  TacticsArgs.(Pair (Int i, Pair (Opt (Message, m1), Opt (Message, m2))))
  s =
  match nth i (goal_as_equiv s) with
  | exception Out_of_range ->
    Tactics.soft_failure (Tactics.Failure "Out of range position")
  | before, e, after ->
    let biframe = List.rev_append before after in
    let table = EquivSequent.table s in
    let system = EquivSequent.system s in
    let env = EquivSequent.env s in

    (* Apply tactic to replace key(s) in [enc] using [new_key].
     * Precondition:
     * [enc = Term.Fun ((fnenc,indices), [m; Term.Name r; k])].
     * Verify that the encryption primitive is used correctly,
     * that the randomness is fresh and that the keys satisfy their SSC. *)
    let apply ~enc ~new_key ~fnenc ~indices ~m ~r ~k =

      let k = Term.head_normal_biterm k in
      (* Verify that key is well-formed, depending on whether encryption is
       * symmetric or not. Return secret key and appropriate SSC. *)
      let ssc,wrap_pk,sk =
        if Symbols.is_ftype fnenc Symbols.SEnc table then
          match Symbols.Function.get_data fnenc table with
            | Symbols.AssociatedFunctions [fndec] ->
              (fun ((sk,isk),system) ->
                Cca.symenc_key_ssc
                  ~system table fnenc fndec
                  ~elems:(goal_as_equiv s) sk;
                Cca.symenc_rnd_ssc ~system table env fnenc sk isk biframe;
                ()
                         )
                ,
                (fun x -> x),
                k
            | _ -> assert false
        else
          match Symbols.Function.get_data fnenc table with
          | Symbols.AssociatedFunctions [fndec;fnpk] ->
             (fun ((sk,_),system) ->
                Euf.key_ssc ~system ~table ~elems:(goal_as_equiv s)
                  ~allow_functions:(fun x -> x = fnpk) fndec sk),
                (fun x -> Term.Fun ((fnpk,indices),[x])),
                begin match k with
                   | Term.Fun ((fnpk',indices'),[sk])
                     when fnpk = fnpk' && indices = indices' -> sk
                   | Term.Fun ((fnpk',indices'),[sk])
                     when fnpk = fnpk' && indices = indices' -> sk
                   | _ ->
                       Tactics.soft_failure
                         (Tactics.Failure
                            "The first encryption is not used \
                             with the correct public key function")
                end
            | _ -> assert false
      in
      let project = function
        | Term.Name n -> n,n
        | Term.(Diff (Name l, Name r)) -> l,r
        | _ ->
            Tactics.soft_failure
              (Tactics.Failure "Secret keys must be names")
      in
      let skl, skr = project sk in
      let (new_skl, new_skr), new_key =
        match new_key with
          | Some k -> project k, k
          | None -> (skl, skl), Term.Name skl
      in

      (* Verify all side conditions, and create the reachability goal
       * for the freshness of [r]. *)
      let random_fresh_cond =
        try
          (* For each key we actually only need to verify the SSC
           * wrt. the appropriate projection of the system. *)
          let sysl = SystemExpr.(project_system PLeft system) in
          let sysr = SystemExpr.(project_system PRight system) in
          List.iter ssc
            (List.sort_uniq Stdlib.compare
               [(skl, sysl); (skr, sysr); (new_skl, sysl); (new_skr, sysr)]) ;
          let context =
            Equiv.subst_equiv [Term.ESubst (enc,Term.empty)] [e]
          in
          fresh_cond system table env (Term.Name r) (context@biframe)
        with Euf.Bad_ssc -> Tactics.soft_failure Tactics.Bad_SSC
      in
      let fresh_goal = trace_seq_of_reach random_fresh_cond s in

      (* Equivalence goal where [enc] is modified using [new_key]. *)
      let new_enc =
        Term.Fun ((fnenc,indices), [m; Term.Name r; wrap_pk new_key])
      in
      let new_elem =
        Equiv.subst_equiv [Term.ESubst (enc,new_enc)] [e]
      in
      let biframe = (List.rev_append before (new_elem @ after)) in

      [Prover.Goal.Trace fresh_goal;
       Prover.Goal.Equiv (EquivSequent.set_equiv_goal s biframe)]

    in

    let target,new_key = match m1,m2 with
      | Some (Message m1), Some (Message m2) -> Some m1, Some m2
      | Some (Message m1), None ->
        begin match m1 with
          | Term.Fun ((f,_),[_;_;_]) -> Some m1, None
          | _ -> None, Some m1
        end
      | None, None -> None, None
      | None, Some _ -> assert false
    in
    match target with
      | Some (Term.Fun ((fnenc,indices),[m; Term.Name r; k]) as enc) ->
        apply ~enc ~new_key ~fnenc ~indices ~m ~r ~k
      | Some _ ->
        Tactics.soft_failure
          (Tactics.Failure ("Target must be of the form enc(_,r,_) where \
                             r is a name"))
      | None ->
        let encs =
          Iter.get_ftypes ~excludesymtype:Symbols.ADec ~system table e Symbols.AEnc @
          Iter.get_ftypes ~excludesymtype:Symbols.SDec ~system table e Symbols.SEnc
        in
        (** Run [apply] on first item in [encs] that is well-formed
          * and has a diff in its key.
          * We could also backtrack in case of failure. *)
        let diff_key = function
          | Term.Diff _ | Term.Fun (_,[Term.Diff _]) -> true
          | _ -> false
        in
        let rec find = function
          | Term.Fun ((fnenc,indices),[m; Term.Name r; k]) as enc :: _
            when diff_key k ->
            apply ~enc ~new_key ~fnenc ~indices ~m ~r ~k
          | _ :: q -> find q
          | [] ->
            Tactics.soft_failure
              (Tactics.Failure ("No subterm of the form enc(_,r,k) where \
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
   TacticsArgs.(Pair (Int, Pair (Opt Message,Opt Message)))

(*------------------------------------------------------------------*)
(** XOR *)

exception Not_xor

(* Removes the first occurence of Name (n,is) in the list l. *)
let rec remove_name_occ n is l = match l with
  | [Name (name,indices); t] when name = n && indices = is -> t
  | [t; Name (name,indices)] when name = n && indices = is -> t
  | _ ->
    Tactics.(soft_failure (Failure "name is not XORed on both sides"))

let mk_xor_if_term_base system table env biframe
    (n_left, is_left, l_left, n_right, is_right, l_right, term) =
  let biframe =
    Equiv.Message (Term.Diff (l_left, l_right)) :: biframe in

  let system_left = SystemExpr.(project_system PLeft system) in
  let phi_left =
    mk_phi_proj system_left table env n_left is_left PLeft biframe
  in

  let system_right = SystemExpr.(project_system PRight system) in
  let phi_right =
    mk_phi_proj system_right table env n_right is_right PRight biframe
  in

  let len_left =
    Term.(Atom (`Message (`Eq,
                          Fun (f_len,[l_left]),
                          Fun (f_len,[Name (n_left,is_left)])))) in

  let len_right =
    Term.(Atom (`Message (`Eq,
                          Fun (f_len,[l_right]),
                          Fun (f_len,[Name (n_right,is_right)])))) in

  let len =
    if len_left = len_right then [len_left] else [len_left;len_right] in

  let phi =
    mk_ands
      (* remove duplicates, and then concatenate *)
      (len @
       List.filter (fun x -> not (List.mem x phi_right)) phi_left @
       phi_right)
  in

  let then_branch = Term.Fun (Term.f_zero,[]) in
  let else_branch = term in
  Equiv.Message Term.(mk_ite phi then_branch else_branch)

let mk_xor_if_term system table env e biframe =
  let (n_left, is_left, l_left, n_right, is_right, l_right, term) =
      begin match e with
      | Equiv.Message t ->
        begin match
          Term.pi_term PLeft t, Term.pi_term PRight t
        with
        | (Fun (fl,[Term.Name (nl,isl);ll]),
           Fun (fr,[Term.Name (nr,isr);lr]))
           when (fl = Term.f_xor && fr = Term.f_xor)
           -> (nl,isl,ll,nr,isr,lr,t)
        | _ -> raise Not_xor
        end
      | Equiv.Formula f -> raise Not_xor
      end
  in

  mk_xor_if_term_base system table env biframe
    (n_left, is_left, l_left, n_right, is_right, l_right, term)


let mk_xor_if_term_name system table env e mess_name biframe =
  let (n_left, is_left, l_left, n_right, is_right, l_right, term) =
      begin match mess_name with
      | n ->
        begin match
          Term.pi_term PLeft n, Term.pi_term PRight n
        with
        | Name (nl,isl), Name (nr,isr) ->
          begin match e with
          | Equiv.Message t ->
            begin match
              Term.pi_term PLeft t, Term.pi_term PRight t
            with
            | (Fun (fl,ll),Fun (fr,lr))
              when (fl = Term.f_xor && fr = Term.f_xor)
              -> (nl,isl,remove_name_occ nl isl ll,
                  nr,isr,remove_name_occ nr isr lr,
                  t)
            | _ -> raise Not_xor
            end
          | Equiv.Formula f -> raise Not_xor
          end
        | _ -> Tactics.soft_failure (Tactics.Failure "Expected a name")
        end
      end
  in
  mk_xor_if_term_base system table env biframe
    (n_left, is_left, l_left, n_right, is_right, l_right, term)


let xor TacticsArgs.(Pair (Int i,
                           Opt (Message, opt_m))) s =
  match nth i (goal_as_equiv s) with
  | before, e, after ->
    (* the biframe to consider when checking the freshness *)
    let biframe = List.rev_append before after in
    let system = EquivSequent.system s in
    let table = EquivSequent.table s in
    let env = EquivSequent.env s in
    let res =
      try
        match opt_m with
        | None -> mk_xor_if_term system table env e biframe
        | Some (TacticsArgs.Message m) ->
          mk_xor_if_term_name system table env e m biframe
      with Not_xor -> 
        Tactics.soft_failure
          (Tactics.Failure
             "Can only apply xor tactic on terms of the form u XOR v")
    in
    begin match res with

    | if_term ->
      let biframe = List.rev_append before (if_term::after) in
      [EquivSequent.set_equiv_goal s biframe]
    end

  | exception Out_of_range ->
    Tactics.soft_failure (Tactics.Failure "Out of range position")


let () =
  T.register_typed "xor"
   ~general_help:"Removes biterm (n(i0,...,ik) XOR t) if n(i0,...,ik) is fresh."
   ~detailed_help:"This yields the same freshness condition on the name as the \
                   fresh tactic."
   ~tactic_group:Cryptographic
   (pure_equiv_typed xor) TacticsArgs.(Pair (Int, Opt Message))


(*------------------------------------------------------------------*)
exception Not_context

class ddh_context ~(system:SystemExpr.system_expr) table exact a b c = object (self)
 inherit Iter.iter_approx_macros ~exact ~system table as super

  method visit_macro mn is a =
    match Symbols.Macro.get_def mn table with
      | Symbols.(Input | Output | State _ | Cond | Exec | Frame) -> ()
      | _ -> super#visit_macro mn is a
  (* we check if the only diff are over g^ab and g^c, and that a, b and c
     appears only as g^a, g^b and g^c. *)
  method visit_message t =
    let g = Term.(Fun (f_g,[])) in
    let exp = Term.f_exp in
    match t with
    (* any name n can occur as g^n *)
    | Term.Fun (f, [g1; Name (n,_)]) when f = exp && g1 = g-> ()
    (* any names a b can occur as g^a^b *)
    | Term.(Diff(Term.(Fun (f1,[(Fun (f2,[g1; Name (n1,_)]));
                     Name (n2,_)
                               ])),
                 Term.Fun (f, [g3; Name (n3,_)])))
      when f1 = exp && f2 = exp && g1 = g && g3=g && n3=c &&
           ((n1 = a && n2 = b) || (n1 = b && n2 = a))
      -> ()
    (* if a name a, b, c appear anywhere else, fail *)
    | Term.Name (n,_) when List.mem n [a; b; c] -> raise Not_context
    (* if a diff is not over a valid ddh diff, we fail  *)
    | Term.Diff _ -> raise Not_context
    | _ -> super#visit_message t

end

exception Macro_found

class find_macros ~(system:SystemExpr.system_expr) table exact  = object (self)
 inherit Iter.iter_approx_macros ~exact ~system table as super

  method visit_macro mn is a =
    match Symbols.Macro.get_def mn table with
    | Symbols.(Input | Output | State _ | Cond | Exec | Frame) ->
      raise Macro_found
    | _ -> self#visit_macro mn is a
end


(** If all the terms of a system can be seen as a context of the terms, where
   all the names appearing inside the terms are only used inside those, returns
   true. *)
let is_ddh_context system table a b c elem_list =
  (* TODO: location *)
  let a,b,c = Symbols.Name.of_lsymb a table,
              Symbols.Name.of_lsymb b table,
              Symbols.Name.of_lsymb c table in
  let iter = new ddh_context ~system table false a b c in
  let iterfm = new find_macros ~system table false in
  let exists_macro =
    try
      List.iter iterfm#visit_term elem_list; false
    with Macro_found -> true
  in
  try
    (* we check that a b and c only occur in the correct form inside the system,
       if the elements contain some macro based on the system.*)
   if exists_macro then
    SystemExpr.iter_descrs table system (
      fun d ->
        iter#visit_formula (snd d.condition) ;
        iter#visit_message (snd d.output) ;
        List.iter (fun (_,t) -> iter#visit_message t) d.updates;
    );
   (* we then check inside the frame *)
    List.iter iter#visit_term elem_list;
    true
  with Not_context | Fresh.Name_found -> false

let ddh (na : lsymb) (nb : lsymb) (nc : lsymb) s sk fk =
  let system = EquivSequent.system s in
  let table = EquivSequent.table s in
  if is_ddh_context system table na nb nc
      (goal_as_equiv s) then
      sk [] fk
    else
      Tactics.soft_failure Tactics.NotDDHContext

(* DDH is called on strings that correspond to names, put potentially without
   the correct arity. E.g, with name a(i), we need to write ddh a, .... Thus, we
   cannot use the typed registering, as a is parsed as a name identifier, which
   then does not have the correct arity. *)

let () = T.register_general "ddh"
    ~tactic_help:{general_help = "Closes the current system, if it is an \
                                  instance of a context of ddh.";
                  detailed_help = "It must be called on strings that corresponds \
                                   to names, but without any indices. It then \
                                   applies ddh to all the copies of the names, \
                                   and checks that all actions of the protocol \
                                   uses the names in a correct way. Can be used \
                                   in collaboration with some transitivity to \
                                   obtain a system where ddh can be applied.";
                  usages_sorts = [Sort (Pair (String, Pair( String, String)))];
                  tactic_group = Cryptographic}
    (function
       | [TacticsArgs.String_name v1;
          TacticsArgs.String_name v2;
          TacticsArgs.String_name v3] ->
         pure_equiv (ddh v1 v2 v3)
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))
