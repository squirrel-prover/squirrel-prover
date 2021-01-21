open Term

type tac = EquivSequent.t Tactics.tac

module T = Prover.EquivTactics

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

(** {2 Tactics} *)

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


(* Admit tactic *)
let () =
  T.register_general "admit"
    ~general_help:"Closes the current goal, or drop a bi-frame element.\
           \n Usage: admit [pos]."
    (function
       | [] -> only_equiv (fun _ sk fk -> sk [] fk)
       | [TacticsArgs.Int_parsed i] ->
           pure_equiv begin fun s sk fk ->
             let before,_,after = nth i (EquivSequent.get_biframe s) in
             let s =
               EquivSequent.set_biframe s (List.rev_append before after)
             in
               sk [s] fk
           end
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))

(** Automatic simplification *)
let simpl =
  Tactics.(
    AndThen
      (Abstract ("fadup",[]) ::
       [Try(
         AndThen [Abstract ("expandall",[]);
                  Abstract ("fadup",[]);
                  OrElse [Abstract ("refl",[]);
                          Abstract ("assumption",[])]])]))

let () =
  T.register_macro "simpl"
    ~general_help:"Automatically simplify the goal.\n Usage: simpl."
    simpl

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
let refl (s : EquivSequent.t) =
  let iter =
    new exist_macros
      ~system:(EquivSequent.get_system s)
      (EquivSequent.get_table s) in
  try
    (* we check that the frame does not contain macro *)
    List.iter iter#visit_term (EquivSequent.get_biframe s);
    if EquivSequent.get_frame Term.Left s = EquivSequent.get_frame Term.Right s
    then
      []
    else
      Tactics.soft_failure (Tactics.NoRefl)
  with
  | NoReflMacros -> Tactics.soft_failure (Tactics.NoReflMacros)

let () =
  T.register "refl"
    ~general_help:"Closes a reflexive goal.\n Usage: refl."
    (only_equiv refl)


(** For each element of the biframe, checks that it is a member of the
  * hypothesis biframe. If so, close the goal. *)
let assumption s =
  let hypothesis = EquivSequent.get_hypothesis_biframe s in
  if List.for_all (fun elem -> List.mem elem hypothesis)
      (EquivSequent.get_biframe s) then
    []
  else
    Tactics.soft_failure (Tactics.Failure "Conclusion different from hypothesis.")

let () =
  T.register "assumption"
    ~general_help:"Close a goal contained in its hypothesis.\n Usage: assump."
    (only_equiv assumption)


(** Given a judgement [s] of the form H0 => E, where E is the conclusion
   biframe, and a timestamp [ts] wich does not occur inside the hypothesis
   H0, produce the judgments H0 => E{ts -> init} and E{ts->pred ts} => E.
   The second one is then direclty simplified by a case on all possible
   values of ts, producing a judgement for each one.
   It would be sound to keep the initial hypothesis H0 in all produced
   subgoals, but equivalence sequents currently support at most one
   hypothesis. *)
let induction TacticsArgs.(Timestamp ts) s =
  let env = EquivSequent.get_env s in
  match ts with
  | Var t as ts ->
    (* Check that variable does not occur in the premise. *)
    if List.exists
         (function
            | EquivSequent.Message m ->
                List.mem (Vars.EVar t) (Term.get_vars m)
            | EquivSequent.Formula m ->
                List.mem (Vars.EVar t) (Term.get_vars m))
         (EquivSequent.get_hypothesis_biframe s)
    then
      Tactics.soft_failure
        (Tactics.Failure "Variable should not occur in the premise");
    (* Remove ts from the sequent, as it will become unused. *)
    let s = EquivSequent.set_env (Vars.rm_var env t) s in
    let table  = EquivSequent.get_table s in
    let system = EquivSequent.get_system s in
    let subst = [Term.ESubst (ts, Pred ts)] in
    let goal = EquivSequent.get_biframe s in
    let hypothesis = EquivSequent.(apply_subst_frame subst goal) in
    let induc_goal = EquivSequent.set_hypothesis_biframe s hypothesis in
    let init_goal =
      EquivSequent.(set_biframe
                      s (apply_subst_frame [Term.ESubst(ts,Init)] goal))
    in
    let goals = ref [] in
    (** [add_action _action descr] adds to goals the goal corresponding to the
      * case where [t] is instantiated by [descr]. *)
    let add_action descr =
      let env = ref @@ EquivSequent.get_env induc_goal in
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
      goals := (EquivSequent.apply_subst ts_subst induc_goal
                |> EquivSequent.set_env !env)
               ::!goals
    in
    SystemExpr.iter_descrs table system add_action ;
    init_goal :: List.rev !goals
  | _  ->
    Tactics.soft_failure
      (Tactics.Failure "expected a timestamp variable")

let () =
  T.register_typed "induction"
    ~general_help:"Apply the induction scheme to the given timestamp.\
           \n Usage: induction t."
    (pure_equiv_typed induction) TacticsArgs.Timestamp
(*
    (function
       | [TacticsArgs.Theory th] ->
           pure_equiv
             (fun s sk fk -> match induction th s with
                | subgoals -> sk subgoals fk
                | exception (Tactics.Tactic_soft_failure e) -> fk e)
       | _ -> Tactics.hard_failure
           (Tactics.Failure "improper arguments"))
*)

let enrich_bool TacticsArgs.(Boolean f) s =
  [EquivSequent.set_biframe s (EquivSequent.Formula f :: EquivSequent.get_biframe s)]

let enrich_mess TacticsArgs.(Message t) s =
  [EquivSequent.set_biframe s (EquivSequent.Message t :: EquivSequent.get_biframe s)]

let () = T.register_typed  "enrich_bool"
    (pure_equiv_typed enrich_bool) TacticsArgs.Boolean

let () = T.register_typed  "enrich_mess"
    (pure_equiv_typed enrich_mess) TacticsArgs.Message

let () = T.register_orelse "enrich"
    ~general_help:"Enrich the goal with the given term.\
           \n Usage: enrich t."
    ["enrich_bool"; "enrich_mess"]

(** Function application *)

exception No_common_head
exception No_FA
let fa_expand t =
  let aux : type a. a Term.term -> EquivSequent.elem list = function
    | Fun (f,l) ->
      List.map (fun m -> EquivSequent.Message m) l
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
        | EquivSequent.Message ITE (c,t,e)
          when (t = Term.Fun(f_true,[]) && e = Term.Fun(f_false,[]))
          -> EquivSequent.Formula c
        | _ -> x)
  in
  match t with
  | EquivSequent.Message e -> filterBoolAsMsg (aux (Term.head_normal_biterm e))
  | EquivSequent.Formula e -> filterBoolAsMsg (aux (Term.head_normal_biterm e))

let fa TacticsArgs.(Int i) s =
  match nth i (EquivSequent.get_biframe s) with
    | before, e, after ->
        begin try
          (* Special case for try find, otherwise we use fa_expand *)
          match e with
          | EquivSequent.Message Find (vars,c,t,e) ->
            let env = ref (EquivSequent.get_env s) in
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
                (EquivSequent.[ Message c' ; Message t' ; Message e ] @ after)
            in
            [ EquivSequent.set_env !env (EquivSequent.set_biframe s biframe) ]
          | _ ->
            let biframe =
              List.rev_append before (fa_expand e @ after) in
              [ EquivSequent.set_biframe s biframe ]
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
    ~general_help:"Break function applications on the nth term of the sequence.\
           \n Usage: fa i."
    (pure_equiv_typed fa) TacticsArgs.Int

(** Check if an element appears twice in the biframe,
  * or if it is [input@t] with some [frame@t'] appearing in the frame
  * with [pred(t) <= t'] guaranteed,
  * or if it is [exec@t] with some [frame@t'] appearing in the frame
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
      | EquivSequent.Message (Term.Macro (im,[],t)) when im = Term.in_macro ->
          List.exists
            (function
               | EquivSequent.Message (Term.Macro (fm,[],t'))
                 when fm = Term.frame_macro && leq (Pred t) t' -> true
               | _ -> false)
            elems
      | EquivSequent.Formula (Term.Macro (em,[],t)) when em = Term.exec_macro ->
          List.exists
            (function
               | EquivSequent.Message (Term.Macro (fm,[],t'))
                 when fm = Term.frame_macro && leq t t' -> true
               | _ -> false)
            elems
      | _ -> false

(** This function goes over all elements inside elems.  All elements that can be
   seen as duplicates, or context of duplicates, are removed. All elements that
   can be seen as context of duplicates and assumptions are removed, but
   replaced by the assumptions that appear as there subterms. *)
let rec filter_fa_dup table res assump elems =
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
  let table = EquivSequent.get_table s in
  let biframe = EquivSequent.get_biframe s
                |> List.rev
                |> filter_fa_dup table [] (EquivSequent.get_hypothesis_biframe s)
  in
  [EquivSequent.set_biframe s biframe]

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
  match nth i (EquivSequent.get_biframe s) with
  | before, e, after ->
      let biframe_without_e = List.rev_append before after in
      let system = EquivSequent.get_system s in
      let table  = EquivSequent.get_table s in
      begin try
        (* we expect that e is of the form exec@pred(tau) && phi *)
        let (tau,phi) =
          let f,g = match e with
            | EquivSequent.Formula Term.And (f,g) -> f,g
            | EquivSequent.Message Term.(Seq (vars,ITE (And (f,g),tt,ff)))
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
          EquivSequent.Message (Term.Macro (Term.frame_macro,[],Term.Pred tau))
        in
        (* we first check that frame@pred(tau) is in the biframe *)
        if List.mem frame_at_pred_tau biframe_without_e then
          (* we iterate over the formula phi to check if it contains only
           * allowed subterms *)
          let iter = new check_fadup ~system table tau in
          iter#check_formula phi ;
          (* on success, we keep only exec@pred(tau) *)
          let new_elem =
            EquivSequent.Formula
              (Term.Macro (Term.exec_macro,[],Term.Pred tau))
          in
          [EquivSequent.set_biframe s (List.rev_append before (new_elem::after))]
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
   ~general_help:"When applied without argument, tries to remove all terms that are \
          duplicates, or context of duplicates. \
          \n When applied on a formula of the form (exec@pred(tau) && phi), \
          with frame@pred(tau) in the biframe, tries to remove phi if it  \
          contains only subterms allowed by the FA-DUP rule.\
          \n Usages: fadup. fadup i."
   (pure_equiv_typed fadup) TacticsArgs.(Opt Int)

(** Fresh *)

exception Name_found
exception Var_found
exception Not_name

class find_name ~(system:SystemExpr.system_expr) table exact name = object (self)
  inherit Iter.iter_approx_macros ~exact ~system table as super

  method visit_message t = match t with
    | Term.Name (n,_) -> if n = name then raise Name_found
    | Term.Var m -> raise Var_found
    | _ -> super#visit_message t
end

class get_name_indices ~(system:SystemExpr.system_expr) table exact name = object (self)
  inherit Iter.iter_approx_macros ~exact ~system table as super

  val mutable indices : (Vars.index list) list = []
  method get_indices = List.sort_uniq Stdlib.compare indices

  method visit_message t = match t with
    | Term.Name (n,is) -> if n = name then indices <- is::indices
    | Term.Var m -> raise Var_found
    | _ -> super#visit_message t
end

class get_actions ~(system:SystemExpr.system_expr) table exact = object (self)
  inherit Iter.iter_approx_macros ~exact ~system table as super

  (* The boolean is set to true only for input macros.
   * In that case, when building phi_proj we require a strict inequality on
   * timestamps because we have to consider only actions occurring before
   * the input.*)
  val mutable actions : (Term.timestamp * bool) list = []
  method get_actions = List.sort_uniq Stdlib.compare actions

  method visit_macro mn is a = match Symbols.Macro.get_def mn table with
    | Symbols.Input -> actions <- (a,true)::actions
    | Symbols.(Output | State _ | Cond | Exec | Frame) ->
      actions <- (a,false)::actions
    | _ -> (actions <- (a, false)::actions; self#visit_macro mn is a)
end

let rec mk_ands = function
  | [] -> Term.True
  | [a] -> a
  | [a; b] -> Term.And(a, b)
  | p::q -> Term.And(p, mk_ands q)

(** Construct the formula expressing freshness for some projection. *)
let mk_phi_proj system table env name indices proj biframe =
  let proj_frame = List.map (EquivSequent.pi_elem proj) biframe in
  begin try
    let list_of_indices_from_frame =
      let iter = new get_name_indices ~system table false name in
        List.iter iter#visit_term proj_frame ;
        iter#get_indices
    and list_of_actions_from_frame =
      let iter = new get_actions ~system table false in
      List.iter iter#visit_term proj_frame ;
      iter#get_actions
    and tbl_of_action_indices = Hashtbl.create 10 in
    SystemExpr.(iter_descrs table system
      (fun action_descr ->
        let iter = new get_name_indices ~system table true name in
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
              List.fold_left Term.mk_or Term.False
                (List.sort_uniq Stdlib.compare
                  (List.map
                    (fun (t,strict) ->
                      if strict
                      then Term.Atom (`Timestamp (`Lt, new_action, t))
                      else Term.Atom (Term.mk_timestamp_leq new_action t))
                    list_of_actions_from_frame))
            (* then indices of name in new_action and of [name] differ *)
            and conj =
              List.fold_left Term.mk_and True
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
  | Name_found ->
      Tactics.soft_failure (Tactics.Failure "Name not fresh")
  | Var_found ->
      Tactics.soft_failure
        (Tactics.Failure "Variable found, unsound to apply fresh")
  end

let fresh_cond system table env t biframe =
  let (n_left, ind_left, n_right, ind_right) =
    match
      Term.pi_term Term.Left t, Term.pi_term Term.Right t
    with
    | (Name (nl,isl), Name (nr,isr)) -> (nl,isl,nr,isr)
    | _ -> raise Not_name
  in
  let system_left = SystemExpr.(project_system Term.Left system) in
  let phi_left =
    mk_phi_proj system_left table env n_left ind_left Term.Left biframe
  in
  let system_right = SystemExpr.(project_system Term.Right system) in
  let phi_right =
    mk_phi_proj system_right table env n_right ind_right Term.Right biframe
  in
  mk_ands
    (* remove duplicates, and then concatenate *)
    ((List.filter (fun x -> not(List.mem x phi_right)) phi_left)
     @
     phi_right)

(** Returns the term if (phi_left && phi_right) then 0 else diff(nL,nR). *)
let mk_if_term system table env e biframe =
  match e with
  | EquivSequent.Message t ->
    let phi = fresh_cond system table env t biframe in
    let then_branch = Term.Fun (Term.f_zero,[]) in
    let else_branch = t in
    EquivSequent.Message Term.(mk_ite phi then_branch else_branch)
  | EquivSequent.Formula f -> raise Not_name

let fresh TacticsArgs.(Int i) s =
  match nth i (EquivSequent.get_biframe s) with
    | before, e, after ->
        (* the biframe to consider when checking the freshness *)
        let biframe = List.rev_append before after in
        let system = EquivSequent.get_system s in
        let table  = EquivSequent.get_table s in
        let env    = EquivSequent.get_env s in
        begin match mk_if_term system table env e biframe with
        | if_term ->
          let biframe = List.rev_append before (if_term::after) in
          [EquivSequent.set_biframe s biframe]
        | exception Not_name ->
          Tactics.soft_failure
            (Tactics.Failure "Can only apply fresh tactic on names")
        end
    | exception Out_of_range ->
        Tactics.soft_failure (Tactics.Failure "Out of range position")

let () =
  T.register_typed "fresh"
    ~general_help:"Removes a name if fresh.\n Usage: fresh i."
    (pure_equiv_typed fresh) TacticsArgs.Int

(* PRF axiom *)

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
      EquivSequent.apply_subst_frame
        [Term.ESubst (hash,Term.Fun (Term.f_zero,[]))]
        [e]
    in
    let frame =
      (EquivSequent.Message t) ::
      (List.map (EquivSequent.pi_elem proj) (e_without_hash @ biframe)) in
    (* check syntactic side condition *)
    Euf.key_ssc
      ~elems:frame ~allow_functions:(fun x -> false)
      ~system ~table hash_fn key_n;
    (* we compute the list of hashes from the frame *)
    let list_of_hashes_from_frame =
      occurrences_of_frame ~system table frame hash_fn key_n
    and list_of_actions_from_frame =
      let iter = new get_actions ~system table false in
      List.iter iter#visit_term frame ;
      iter#get_actions
    and tbl_of_action_hashes = Hashtbl.create 10 in
    (* we iterate over all the actions of the (single) system *)
    SystemExpr.(iter_descrs table system
      (fun action_descr ->
        (* we add only actions in which a hash occurs *)
        let descr_proj = Action.pi_descr proj action_descr in
        let action_hashes =
          occurrences_of_action_descr ~system table descr_proj hash_fn key_n in
        if List.length action_hashes > 0 then
          Hashtbl.add tbl_of_action_hashes descr_proj action_hashes));
    (* direct cases (for explicit occurences of hashes in the frame) *)
    let phi_frame =
      (List.map
        (fun (is,m) ->
          (* select bound variables in key indices [is] and in message [m]
          * to quantify universally over them *)
          let env = ref env in
          let vars = Term.get_vars m in
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
              List.fold_left Term.mk_or Term.False
                (List.sort_uniq Stdlib.compare
                  (List.map
                    (fun (t,strict) ->
                      if strict
                      then Term.Atom (`Timestamp (`Lt, new_action, t))
                      else Term.Atom (Term.mk_timestamp_leq new_action t))
                    list_of_actions_from_frame))
            (* then if key indices are equal then hashed messages differ *)
            and conj =
              List.fold_left Term.mk_and True
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
  | Euf.Bad_ssc -> Tactics.soft_failure
    (Tactics.Failure "Key syntactic side condition not checked")
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
  match nth i (EquivSequent.get_biframe s) with
    | before, e, after ->
      let biframe = List.rev_append before after in
      let system = (EquivSequent.get_system s) in
      let table = EquivSequent.get_table s in
      let env = EquivSequent.get_env s in
      let e = match e with
        | EquivSequent.Message m ->
          EquivSequent.Message (Term.head_normal_biterm m)
        | EquivSequent.Formula f ->
          EquivSequent.Formula (Term.head_normal_biterm f)
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
            mk_prf_phi_proj Term.Left system table env biframe e hash in
          let phi_right =
            mk_prf_phi_proj Term.Right system table env biframe e hash in
          let table,n = Symbols.Name.declare table "n_PRF" 0 in
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
                      Term.And (Term.Not f,  combine_conj_formulas phi_left phi_right)
                    | _ -> assert false
          in
          let if_term =
            Term.ITE
              (final_if_formula,
              Term.Name (n,[]),
              hash) in
          let new_elem =
            EquivSequent.apply_subst_frame [Term.ESubst (hash,if_term)] [e] in
          let biframe = (List.rev_append before (new_elem @ after)) in
          [EquivSequent.set_biframe s biframe]
      | _ -> assert false
      end
    | exception Out_of_range ->
        Tactics.soft_failure (Tactics.Failure "Out of range position")

let () =
  T.register_typed "prf"
    ~general_help:"Apply the PRF axiom.\n Usage: prf i."
    (pure_equiv_typed prf) TacticsArgs.Int

(** Symmetric encryption **)

class check_symenc_key ~system table enc_fn dec_fn key_n = object (self)
  inherit Iter.iter_approx_macros ~exact:false ~system table as super
  method visit_message t = match t with
    | Term.Fun ((fn,_), [m;r; Term.Name _]) when fn = enc_fn ->
      self#visit_message m; self#visit_message r
    | Term.Fun ((fn,_), [m; Term.Name _]) when fn = dec_fn ->
      self#visit_message m
    | Term.Fun ((fn,_), [m;r; Diff(Term.Name _, Term.Name _)]) when fn = enc_fn ->
      self#visit_message m; self#visit_message r
    | Term.Fun ((fn,_), [m;  Diff(Term.Name _, Term.Name _)]) when fn = dec_fn ->
      self#visit_message m
    | Term.Name (n,_) when n = key_n -> raise Euf.Bad_ssc
    | Term.Var m -> raise Euf.Bad_ssc
    | _ -> super#visit_message t
end

let symenc_key_ssc ?(messages=[]) ?(elems=[]) ~system table enc_fn dec_fn key_n =
  let ssc = new check_symenc_key ~system table enc_fn dec_fn key_n in
  List.iter ssc#visit_message messages ;
  List.iter ssc#visit_term elems ;
  SystemExpr.(iter_descrs table system
    (fun action_descr ->
       ssc#visit_formula (snd action_descr.condition) ;
       ssc#visit_message (snd action_descr.output) ;
       List.iter (fun (_,t) -> ssc#visit_message t) action_descr.updates))



(* Iterator to check that the given randoms are only used in random seed
   position for encryption. *)
class check_rand ~allow_vars ~system table enc_fn randoms = object (self)
  inherit Iter.iter_approx_macros ~exact:false ~system table as super
  method visit_message t = match t with
    | Term.Fun ((fn,_), [m1;Term.Name _; m2]) when fn = enc_fn ->
      self#visit_message m1; self#visit_message m2
    | Term.Fun ((fn,_), [m1; _; m2]) when fn = enc_fn ->
      raise Euf.Bad_ssc
    | Term.Name (n,_) when List.mem n randoms ->
      Tactics.soft_failure (Tactics.SEncRandomNotFresh)
    | Term.Var m -> if not(allow_vars) then
        Tactics.soft_failure (Tactics.Failure "No universal quantification over \
                                               messages allowed")
    | _ -> super#visit_message t
end

(* Check that the given randoms are only used in random seed position for
   encryption. *)
let random_ssc ?(allow_vars=false) ?(messages=[]) ?(elems=[]) ~system table enc_fn randoms =
  let ssc = new check_rand ~allow_vars ~system table enc_fn randoms in
  List.iter ssc#visit_message messages;
  List.iter ssc#visit_term elems;
  SystemExpr.(iter_descrs table system
    (fun action_descr ->
       ssc#visit_formula (snd action_descr.condition) ;
       ssc#visit_message (snd action_descr.output) ;
       List.iter (fun (_,t) -> ssc#visit_message t) action_descr.updates))


  (* Given cases produced by an Euf.mk_rule for some symmetric encryption
     scheme, check that all occurences of the encryption use a dedicated
     randomness.
     It checks that:
      - a randomness is only used inside a randomness position
      - there does not exists two messages from different place with the
     same randomness
      - if inside an action A[I], the encryption enc(m,r,sk) is produced,
       the index variables appearing in both m and I should also appear in r.

     This could be refined into a tactic where we ask to prove that encryptions
     that use the same randomness are done on the same plaintext. This is why we
     based ourselves on messages produced by Euf.mk_rule, which should simplify
     such extension if need. *)
let check_encryption_randomness system table case_schemata cases_direct enc_fn messages elems =
  let encryptions : (Term.message * Vars.index list) list
    = List.map (fun case -> case.Euf.message,
                                          case.Euf.action_descr.indices) case_schemata
                    @
                    List.map (fun case -> case.Euf.d_message, []) cases_direct
  in
  let encryptions = List.sort_uniq Stdlib.compare encryptions in
  let randoms = List.map (function
      | Fun ((_, _), [_; Name (r, is); _]), _-> r
      | _ ->  Tactics.soft_failure (Tactics.SEncNoRandom))
      encryptions
  in
  random_ssc ~elems ~messages ~system table enc_fn randoms;
  (* we check that encrypted messages based on indices, do not depend on free
     indices instantiated by the action w.r.t the indices of the random. *)
  if List.exists (function
      | (Fun ((_, _), [m; Name (_, is); _]), (actidx:Vars.index list)) ->
        let vars = Term.get_vars m in
        List.exists (function
            Vars.EVar v ->
              (match Vars.sort v with
                |Sorts.Index -> (List.mem v actidx) && not (List.mem v is)
                (* we fail if there exists an indice appearing in the message,
                   which is an indice instantiated by the action description,
                   and it does not appear in the random. *)
               | _ -> false)) vars
      | _ -> assert false) encryptions then
    Tactics.soft_failure (Tactics.SEncSharedRandom);

  (* we check that no encryption is shared between multiple encryptions *)
  let enc_classes = Utils.classes (fun m1 m2 ->
      match m1, m2 with
      | (Fun ((_, _), [_; Name (r, is); _]),_), (Fun ((_, _), [_; Name (r2,is2); _]),_)
        -> (r = r2)
      (* the patterns should match, if they match inside the declaration of randoms *)
      | _ -> assert false
    ) encryptions in
  if List.exists (fun l -> List.length l > 1) enc_classes then
    Tactics.soft_failure (Tactics.SEncSharedRandom)


let symenc_rnd_ssc ~system table env head_fn key_n key_is elems =
  let rule =
    Euf.mk_rule ~elems ~drop_head:false ~allow_functions:(fun x -> false)
      ~system ~table ~env ~mess:Term.empty ~sign:Term.empty
      ~head_fn ~key_n ~key_is
  in
  check_encryption_randomness system table
    rule.Euf.case_schemata rule.Euf.cases_direct head_fn [] elems

(** CCA1 *)

let cca1 TacticsArgs.(Int i) s =
  match nth i (EquivSequent.get_biframe s) with
  | before, e, after ->
    let biframe = List.rev_append before after in
    let system = (EquivSequent.get_system s) in
    let table = EquivSequent.get_table s in
    let env = EquivSequent.get_env s in
    let e = match e with
      | EquivSequent.Message m ->
        EquivSequent.Message (Term.head_normal_biterm m)
      | EquivSequent.Formula f ->
        EquivSequent.Formula (Term.head_normal_biterm f)
    in
    let get_subst_hide_enc enc fnenc m fnpk sk fndec r eis isk  is_top_level=
      (* we check that the random is fresh, and the key satisfy the
               side condition. *)
      begin

          (* we create the fresh cond reachability goal *)
          let random_fresh_cond = fresh_cond system table env (Term.Name r) biframe in
          let fresh_goal = Prover.Goal.Trace
              (TraceSequent.init ~system table random_fresh_cond
               |> TraceSequent.set_env env
              )
          in
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
   | EquivSequent.Message (Term.Fun ((fnenc,eis), [m; Term.Name r;
                                    Term.Fun ((fnpk,is), [Term.Name (sk,isk)])]))
              when (Symbols.is_ftype fnpk Symbols.PublicKey table
                    && Symbols.is_ftype fnenc Symbols.AEnc table) -> true
   | EquivSequent.Message (Term.Fun ((fnenc,eis), [m; Term.Name r; Term.Name (sk,isk)]))
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
                if not (List.mem (EquivSequent.Message
                                    (Term.Fun ((fnpk,is), [Term.Name (sk,isk)]))
                                 ) biframe) then
                  Tactics.soft_failure
                    (Tactics.Failure
                       "The public key must be inside the frame in order to use \
                        CCA1")
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
                 "The first encryption symbol is not used with the correct public \
                  key function.")
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
                symenc_key_ssc  ~elems:(EquivSequent.get_biframe s) ~messages:[enc]
                  ~system table fnenc fndec sk;
                (* we check that the randomness is ok in the system and the
                   biframe, except for the encryptions we are looking at, which
                   is checked by adding a fresh reachability goal. *)
                symenc_rnd_ssc ~system table env fnenc sk isk biframe;
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
    let new_elem =    EquivSequent.apply_subst_frame substs [e] in
    let biframe = (List.rev_append before (new_elem @ after)) in
     Prover.Goal.Equiv (EquivSequent.set_biframe s biframe) :: fgoals

  | exception Out_of_range ->
    Tactics.soft_failure (Tactics.Failure "Out of range position")


let () =
 T.register_typed "cca1"
   ~general_help:"Apply the cca1 axiom on all encryptions of the given message. \
          Encryption at toplevel are replaced by the length of the \
          plaintext. \
          Encryption not at toplevel are replaced by the encryption of the \
          length of the plaintexts. \
          \n Usage: cca1 i."
   (only_equiv_typed cca1) TacticsArgs.Int

(** Encryption key privacy  *)

let enckp
  TacticsArgs.(Pair (Int i, Pair (Opt (Message, m1), Opt (Message, m2))))
  s =
  match nth i (EquivSequent.get_biframe s) with
  | exception Out_of_range ->
    Tactics.soft_failure (Tactics.Failure "Out of range position")
  | before, e, after ->
    let biframe = List.rev_append before after in
    let table = EquivSequent.get_table s in
    let system = EquivSequent.get_system s in
    let env = EquivSequent.get_env s in

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
                symenc_key_ssc
                  ~system table fnenc fndec
                  ~elems:(EquivSequent.get_biframe s) sk;
                symenc_rnd_ssc ~system table env fnenc sk isk biframe;
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
                Euf.key_ssc ~system ~table ~elems:(EquivSequent.get_biframe s)
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
          let sysl = SystemExpr.(project_system Term.Left system) in
          let sysr = SystemExpr.(project_system Term.Right system) in
          List.iter ssc
            (List.sort_uniq Stdlib.compare
               [(skl, sysl); (skr, sysr); (new_skl, sysl); (new_skr, sysr)]) ;
          let context =
            EquivSequent.apply_subst_frame [Term.ESubst (enc,Term.empty)] [e]
          in
          fresh_cond system table env (Term.Name r) (context@biframe)
        with Euf.Bad_ssc -> Tactics.soft_failure Tactics.Bad_SSC
      in
      let fresh_goal =
        Prover.Goal.Trace
          (TraceSequent.init ~system table random_fresh_cond
           |> TraceSequent.set_env env)
      in

      (* Equivalence goal where [enc] is modified using [new_key]. *)
      let new_enc =
        Term.Fun ((fnenc,indices), [m; Term.Name r; wrap_pk new_key])
      in
      let new_elem =
        EquivSequent.apply_subst_frame [Term.ESubst (enc,new_enc)] [e]
      in
      let biframe = (List.rev_append before (new_elem @ after)) in

      [fresh_goal;
       Prover.Goal.Equiv (EquivSequent.set_biframe s biframe)]

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
   ~general_help:"Change key in some encryption subterm. \
          The term and new key can be passed as arguments, \
          otherwise the tactic applies to the first subterm of the form \
          enc(_,r,k) where r is a name and k features a diff operator.\
          \n Usage: enckp i,[target],[newkey]."
   (only_equiv_typed enckp)
   TacticsArgs.(Pair (Int, Pair (Opt Message,Opt Message)))

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
    EquivSequent.Message (Term.Diff (l_left, l_right)) :: biframe in
  let system_left = SystemExpr.(project_system Term.Left system) in
  let phi_left =
    mk_phi_proj system_left table env n_left is_left Term.Left biframe
  in
  let system_right = SystemExpr.(project_system Term.Right system) in
  let phi_right =
    mk_phi_proj system_right table env n_right is_right Term.Right biframe
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
  EquivSequent.Message Term.(mk_ite phi then_branch else_branch)

let mk_xor_if_term system table env e biframe =
  let (n_left, is_left, l_left, n_right, is_right, l_right, term) =
      begin match e with
      | EquivSequent.Message t ->
        begin match
          Term.pi_term Term.Left t, Term.pi_term Term.Right t
        with
        | (Fun (fl,[Term.Name (nl,isl);ll]),
           Fun (fr,[Term.Name (nr,isr);lr]))
           when (fl = Term.f_xor && fr = Term.f_xor)
           -> (nl,isl,ll,nr,isr,lr,t)
        | _ -> raise Not_xor
        end
      | EquivSequent.Formula f -> raise Not_xor
      end
  in
  mk_xor_if_term_base system table env biframe
    (n_left, is_left, l_left, n_right, is_right, l_right, term)

let mk_xor_if_term_name system table env e mess_name biframe =
  let (n_left, is_left, l_left, n_right, is_right, l_right, term) =
      begin match mess_name with
      | n ->
        begin match
          Term.pi_term Term.Left n, Term.pi_term Term.Right n
        with
        | Name (nl,isl), Name (nr,isr) ->
          begin match e with
          | EquivSequent.Message t ->
            begin match
              Term.pi_term Term.Left t, Term.pi_term Term.Right t
            with
            | (Fun (fl,ll),Fun (fr,lr))
              when (fl = Term.f_xor && fr = Term.f_xor)
              -> (nl,isl,remove_name_occ nl isl ll,
                  nr,isr,remove_name_occ nr isr lr,
                  t)
            | _ -> raise Not_xor
            end
          | EquivSequent.Formula f -> raise Not_xor
          end
        | _ -> Tactics.soft_failure (Tactics.Failure "Expected a name")
        end
      end
  in
  mk_xor_if_term_base system table env biframe
    (n_left, is_left, l_left, n_right, is_right, l_right, term)


let xor TacticsArgs.(Pair (Int i,
                           Opt (Message, opt_m))) s =
  match nth i (EquivSequent.get_biframe s) with
  | before, e, after ->
    (* the biframe to consider when checking the freshness *)
    let biframe = List.rev_append before after in
    let system = EquivSequent.get_system s in
    let table = EquivSequent.get_table s in
    let env = EquivSequent.get_env s in
    let res =
      try
        match opt_m with
        | None -> mk_xor_if_term system table env e biframe
        | Some (TacticsArgs.Message m) ->
          mk_xor_if_term_name system table env e m biframe
      with Not_xor -> Tactics.soft_failure
                        (Tactics.Failure
                           "Can only apply xor tactic on terms of the form u XOR v")
    in
    begin match res with
    | if_term ->
      let biframe = List.rev_append before (if_term::after) in
      [EquivSequent.set_biframe s biframe]
    end
  | exception Out_of_range ->
    Tactics.soft_failure (Tactics.Failure "Out of range position")


let () =
 T.register_typed "xor"
   ~general_help:"Removes biterm (n(i0,...,ik) XOR t) if n(i0,...,ik) is fresh.
          \n Usage without giving the fresh name (should be xor's first
          argument): xor i.
          \n Usage giving the fresh name: xor i, n(i0,...,ik)."
   (pure_equiv_typed xor) TacticsArgs.(Pair (Int, Opt Message))

(* Sequence expansion of the sequence [term] for the given parameters [ths]. *)
let expand_seq (term:Theory.term) (ths:Theory.term list) (s:EquivSequent.t) =
  let env = EquivSequent.get_env s in
  let table = EquivSequent.get_table s in
  let tsubst = Theory.subst_of_env env in
  let conv_env = Theory.{ table = table; cntxt = InGoal; } in
  match Theory.convert conv_env tsubst term Sorts.Message with
  (* we expect term to be a sequence *)
  | Seq ( vs, t) ->
    let vs = List.map (fun x -> Vars.EVar x) vs in
    (* we parse the arguments ths, to create a substution for variables vs *)
    let subst = Theory.parse_subst table env vs ths in
    (* new_t is the term of the sequence instantiated with the subst *)
    let new_t = EquivSequent.Message (Term.subst subst t) in
    (* we add the new term to the frame and the hypothesis if it does not yet
       belongs to it *)
    let biframe =
      let old_biframe = EquivSequent.get_biframe s in
      if List.mem new_t old_biframe then old_biframe else new_t :: old_biframe
    in
    let hypo_biframe =
      let old_hyp_biframe = EquivSequent.get_hypothesis_biframe s in
      if List.mem new_t old_hyp_biframe then old_hyp_biframe
      else new_t :: old_hyp_biframe
    in
    [ EquivSequent.set_biframe
        (EquivSequent.set_hypothesis_biframe s hypo_biframe)
        biframe]
  | _ ->
    Tactics.soft_failure
      (Tactics.Failure "can only expand with sequences with parameters")
  | exception Theory.(Conv e) ->
    Tactics.soft_failure (Cannot_convert e)

(* Expand all occurrences of the given macro [term] inside [s] *)
let expand (term : Theory.term) (s : EquivSequent.t) =
  let tsubst = Theory.subst_of_env (EquivSequent.get_env s) in
  (* final function once the subtitustion has been computed *)
  let succ subst =
    let apply_subst = function
      | EquivSequent.Message e -> EquivSequent.Message (Term.subst subst e)
      | EquivSequent.Formula e -> EquivSequent.Formula (Term.subst subst e)
    in
    [EquivSequent.set_biframe s
      (List.map apply_subst (EquivSequent.get_biframe s))]
  in
  let table = EquivSequent.get_table s in
  (* computes the substitution dependeing on the sort of term *)
  let conv_env = Theory.{ table = table; cntxt = InGoal; } in
  match Theory.convert conv_env tsubst term Sorts.Boolean with
    | Macro ((mn, sort, is),l,a) ->
      if Macros.is_defined mn a table then
        succ [Term.ESubst (Macro ((mn, sort, is),l,a),
                           Macros.get_definition
                             (EquivSequent.get_system s) table sort mn is a)]
      else Tactics.soft_failure (Tactics.Failure "cannot expand this macro")
    | _ ->
      Tactics.soft_failure (Tactics.Failure "can only expand macros")
    | exception Theory.(Conv (Type_error _)) ->
      begin
        match Theory.convert conv_env tsubst term Sorts.Message with
        | Macro ((mn, sort, is),l,a) ->
          if Macros.is_defined mn a table then
            succ [Term.ESubst (Macro ((mn, sort, is),l,a),
                               Macros.get_definition
                                 (EquivSequent.get_system s) table sort mn is a)]
          else Tactics.soft_failure (Tactics.Failure "cannot expand this macro")
        | _ ->
          Tactics.soft_failure (Tactics.Failure "can only expand macros")
        | exception Theory.(Conv e) ->
          Tactics.soft_failure (Cannot_convert e)
      end
    | exception Theory.(Conv e) ->
      Tactics.soft_failure (Cannot_convert e)

(* Does not rely on the typed registering, as it parsed a substitution. *)
let () = T.register_general "expand"
  ~general_help:"Expand all occurrences of the given macro, or expand the given \
         sequence using the given indices.\
         \n Usage: expand macro. expand seq(i,k...->t(i,k,...)),i1,k1,..."
  (function
    | [TacticsArgs.Theory v] ->
        pure_equiv
          (fun s sk fk -> match expand v s with
             | subgoals -> sk subgoals fk
             | exception (Tactics.Tactic_soft_failure e) -> fk e)
    | (TacticsArgs.Theory v)::ids ->
        let ids =
          List.map
            (function
               | TacticsArgs.Theory th -> th
               | _ -> Tactics.hard_failure
                        (Tactics.Failure "improper arguments"))
            ids
        in
        pure_equiv
          (fun s sk fk -> match expand_seq v ids s with
             | subgoals -> sk subgoals fk
             | exception (Tactics.Tactic_soft_failure e) -> fk e)
     | _ ->
         Tactics.hard_failure
           (Tactics.Failure "improper arguments"))

(** Expands all macro occurrences inside the biframe, if the macro is not at
  * some pred(A) but about at a concrete action.
  * Acts recursively, also expanding the macros inside macro definition. *)
let expand_all () s =
  let expand_all_macros t system table =
    let rec aux : type a. a term -> a term = function
      | Macro ((mn, sort, is),l,a) when Macros.is_defined mn a table ->
                aux (Macros.get_definition system table sort mn is a)
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
      | Init -> Init
      | Pred _ as a -> a
      | Action _ as a -> a
    in
    aux t
  in
  let system = EquivSequent.get_system s in
  let table  = EquivSequent.get_table s in
  let expand_all_macros = function
    | EquivSequent.Message e ->
      EquivSequent.Message (expand_all_macros e system table)
    | EquivSequent.Formula e ->
      EquivSequent.Formula (expand_all_macros e system table)
  in
  let biframe = EquivSequent.get_biframe s
                |> List.map (expand_all_macros)
  in
  [EquivSequent.set_biframe s biframe]

let () = T.register "expandall"
    ~general_help:"Expand all occurrences of macros that are about explicit actions.
           \n Usage: expandall."
         (pure_equiv_typed expand_all ())


(** Replace all occurrences of [t1] by [t2] inside of [s],
  * and add a subgoal to prove that [t1 <=> t2]. *)
let equiv_formula TacticsArgs.(Pair (Boolean f1, Boolean f2)) (s : EquivSequent.t) =
  let env = EquivSequent.get_env s in
  let system = EquivSequent.get_system s in
  let table  = EquivSequent.get_table s in
    (* goal for the equivalence of t1 and t2 *)
    let trace_sequent =
      TraceSequent.init ~system table
        (Term.And(Term.Impl(f1, f2), Term.Impl(f2, f1)))
      |> TraceSequent.set_env env
    in
    let subgoals =
      [ Prover.Goal.Trace trace_sequent;
        Prover.Goal.Equiv
          (EquivSequent.apply_subst [Term.ESubst (f1,f2)] s) ]
    in
    subgoals

(** Replace all occurrences of [m1] by [m2] inside of [s],
  * and add a subgoal to prove that [Eq(m1, m2)]. *)
let equiv_message TacticsArgs.(Pair (Message m1, Message m2)) (s : EquivSequent.t) =
  let env = EquivSequent.get_env s in
  let system = EquivSequent.get_system s in
  let table = EquivSequent.get_table s in
    (* goal for the equivalence of t1 and t2 *)
    let trace_sequent =
      TraceSequent.init ~system table
        (Term.Atom (`Message (`Eq,m1,m2)))
      |> TraceSequent.set_env env
    in
    let subgoals =
      [ Prover.Goal.Trace trace_sequent;
        Prover.Goal.Equiv
          (EquivSequent.apply_subst [Term.ESubst (m1,m2)] s) ]
    in
    subgoals

let () = T.register_typed "equiv_mess" (only_equiv_typed equiv_message)
    TacticsArgs.(Pair (Message, Message))

let () = T.register_typed "equiv_formula" (only_equiv_typed equiv_formula)
    TacticsArgs.(Pair (Boolean, Boolean))

let () = T.register_orelse "equivalent"
  ~general_help:"Replace all occurrences of a formula by another, and ask to prove \
         \n that they are equivalent.
         \n Usage: equiv t1, t2."
  ["equiv_formula"; "equiv_mess"]

let simplify_ite b env system table cond positive_branch negative_branch =
  if b then
    (* replace in the biframe the ite by its positive branch *)
    (* ask to prove that the cond of the ite is True *)
    let trace_sequent = TraceSequent.init ~system table cond
      |> TraceSequent.set_env env
    in
    (positive_branch, trace_sequent)
  else
    (* replace in the biframe the ite by its negative branch *)
    (* ask to prove that the cond of the ite implies False *)
    let trace_sequent = TraceSequent.init ~system table (Term.Impl(cond,False))
      |> TraceSequent.set_env env
    in
    (negative_branch, trace_sequent)

class get_ite_term ~system table = object (self)
  inherit Iter.iter_approx_macros ~exact:true ~system table as super
  val mutable ite : (Term.formula * Term.message * Term.message) option = None
  method get_ite = ite
  method visit_message = function
    | Term.ITE (c,t,e) ->
        ite <- Some (c,t,e)
    | m -> super#visit_message m
end
(** [get_ite ~system table elem] returns None if there is no ITE term in [elem],
    Some ite otherwise, where [ite] is the first ITE term encountered.
    Does not explore macros. *)
let get_ite ~system table elem =
  let iter = new get_ite_term ~system table in
  List.iter iter#visit_term [elem];
  iter#get_ite

let yes_no_if b TacticsArgs.(Int i) s =
  let env = EquivSequent.get_env s in
  let system = EquivSequent.get_system s in
  let table = EquivSequent.get_table s in
  match nth i (EquivSequent.get_biframe s) with
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
          simplify_ite b env system table c t e in
        let new_elem =
          EquivSequent.apply_subst_frame
            [Term.ESubst (Term.ITE (c,t,e),branch)]
            [elem]
        in
        let biframe = List.rev_append before (new_elem @ after) in
        [ Prover.Goal.Trace trace_sequent;
          Prover.Goal.Equiv (EquivSequent.set_biframe s biframe) ]
    end
  | exception Out_of_range ->
     Tactics.soft_failure (Tactics.Failure "out of range position")

let () =
 T.register_typed "noif"
   ~general_help:"Try to prove diff equivalence by proving that the condition at the \
          \n i-th position implies False.\
          \n Usage: noif i."
   (only_equiv_typed (yes_no_if false)) TacticsArgs.Int

let () =
 T.register_typed "yesif"
   ~general_help:"Try to prove diff equivalence by proving that the condition at the \
          \n i-th position is True.\
          \n Usage: yesif i."
   (only_equiv_typed (yes_no_if true)) TacticsArgs.Int

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
  match nth i (EquivSequent.get_biframe s) with
  | before, e, after ->
    let cond, positive_branch, negative_branch =
      match e with
      | EquivSequent.Message ITE (c,t,e) -> (c, t, e)
      | _ ->  Tactics.soft_failure
                (Tactics.Failure "can only be applied to a conditional")
    in
    let env = EquivSequent.get_env s in
    let system = EquivSequent.get_system s in
    let table = EquivSequent.get_table s in
      begin try
        let new_elem = EquivSequent.Message
          (ITE (cond, push_formula j f positive_branch, negative_branch))
        in
        let biframe = List.rev_append before (new_elem :: after) in
        let trace_sequent = TraceSequent.init ~system table Term.(Impl(cond, f))
          |> TraceSequent.set_env env in
        [ Prover.Goal.Trace trace_sequent;
          Prover.Goal.Equiv (EquivSequent.set_biframe s biframe) ]
      with
      | Not_ifcond ->
          Tactics.soft_failure (Tactics.Failure "tactic not applicable because \
          the formula contains variables that overlap with variables bound by \
          a seq or a try find construct")
      end
  | exception Out_of_range ->
    Tactics.soft_failure (Tactics.Failure "out of range position")



let () =
  T.register_typed "ifcond"
    ~general_help: "If the given conditional implies that the given formula f is true, \
            push the formula f at top-level in all the subterms of the then \
            branch. \
            If the int parameter j is given, will push the formula only in the \
            jth subterm of the then branch (zero-based). \
            \n Usage: ifcond i,f. ifcond i,j,f."
   (only_equiv_typed ifcond) TacticsArgs.(Pair (Int, Pair( Opt Int, Boolean)))

let trivial_if (TacticsArgs.Int i) s =
  let env = EquivSequent.get_env s in
  let system = EquivSequent.get_system s in
  let table = EquivSequent.get_table s in
  match nth i (EquivSequent.get_biframe s) with
  | before, elem, after ->
    (* search for the first occurrence of an if-then-else in [elem] *)
    begin match get_ite ~system table elem with
    | None ->
      Tactics.soft_failure
        (Tactics.Failure
          "can only be applied on a term with at least one occurrence \
           of an if then else term")
    | Some (c,t,e) ->
      let trace_goal  = Prover.Goal.Trace
          (TraceSequent.init ~system table (Term.Atom (`Message (`Eq,t,e)))
           |> TraceSequent.set_env env
          )
      in
      let new_elem =
        EquivSequent.apply_subst_frame
          [Term.ESubst (Term.ITE (c,t,e),t)]
          [elem]
      in
      let biframe = List.rev_append before (new_elem @ after) in
      [ trace_goal;
        Prover.Goal.Equiv (EquivSequent.set_biframe s biframe) ]
    end
  | exception Out_of_range ->
     Tactics.soft_failure (Tactics.Failure "out of range position")

let () =
 T.register_typed "trivialif"
   ~general_help:"Simplify a conditional when the two branches are equal.\
          \n Usage: trivialif i."
   (only_equiv_typed trivial_if) TacticsArgs.Int

(* allows to replace inside the positive branch of an if then else a term by
   another, if the condition implies there equality. *)
let ifeq
    TacticsArgs.(Pair (Int i, Pair (Message t1, Message t2)))
    s
  =
  match nth i (EquivSequent.get_biframe s) with
  | before, e, after ->
    let cond, positive_branch, negative_branch =
      match e with
      | EquivSequent.Message ITE (c,t,e) ->
        (c, t, e)
      | _ -> Tactics.soft_failure
               (Tactics.Failure "Can only be applied to a conditional.")
    in
    let env = EquivSequent.get_env s in
    let system = EquivSequent.get_system s in
    let table = EquivSequent.get_table s in
      let new_elem =
        EquivSequent.Message (ITE (cond,
                                   Term.subst [Term.ESubst (t1,t2)] positive_branch,
                                   negative_branch))
      in
      let biframe = List.rev_append before (new_elem :: after) in
      let trace_sequent = TraceSequent.init ~system table
          Term.(Impl(cond, Atom (`Message (`Eq,t1,t2))))
                          |> TraceSequent.set_env env in
      [ Prover.Goal.Trace trace_sequent;
           Prover.Goal.Equiv (EquivSequent.set_biframe s biframe) ]
  | exception Out_of_range ->
     Tactics.soft_failure (Tactics.Failure "Out of range position")

let () = T.register_typed "ifeq"
    ~general_help:"If the given conditional implies the equality of the two given terms,\
           substitute the first one by the second one inside the positive branch\
           of the conditional.
           \n Usage: ifeq i,t1,t2."
    (only_equiv_typed ifeq) TacticsArgs.(Pair (Int, Pair (Message, Message)))


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
  let a,b,c = Symbols.Name.of_string a table,
              Symbols.Name.of_string b table,
              Symbols.Name.of_string c table in
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
  with Not_context | Name_found -> false

let ddh na nb nc s sk fk =
  let system = EquivSequent.get_system s in
  let table = EquivSequent.get_table s in
  if is_ddh_context system table na nb nc
      (EquivSequent.get_biframe s) then
      sk [] fk
    else
      Tactics.soft_failure Tactics.NotDDHContext

(* DDH is called on strings that correspond to names, put potentially without
   the correct arity. E.g, with name a(i), we need to write ddh a, .... Thus, we
   cannot use the typed registering, as a is parsed as a name identifier, which
   then does not have the correct arity. *)

let () = T.register_general "ddh"
    ~general_help:"Closes the current system, if it is an instance of a context of ddh.\
           \n Usage: ddh a, b, c."
    (function
       | [TacticsArgs.String_name v1;
          TacticsArgs.String_name v2;
          TacticsArgs.String_name v3] ->
         pure_equiv (ddh v1 v2 v3)
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))
