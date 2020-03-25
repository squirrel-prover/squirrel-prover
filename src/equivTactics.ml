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
let only_equiv t (s : Prover.Goal.t) sk fk =
  match s with
  | Prover.Goal.Equiv s -> t s sk fk
  | _ -> fk (Tactics.Failure "Equivalence goal expected")

(** Wrap a tactic expecting and returning equivalence goals
  * into a general prover tactic. *)
let pure_equiv t s sk fk =
  let t' s sk fk =
    t s (fun l fk -> sk (List.map (fun s -> Prover.Goal.Equiv s) l) fk) fk
  in
  only_equiv t' s sk fk

(* Admit tactic *)
let () =
  T.register_general "admit"
    ~help:"Closes the current goal, or frop a bi-frame element.\
           \n Usage: admit [pos]."
    (function
       | [] -> only_equiv (fun _ sk fk -> sk [] fk)
       | [Prover.Int i] ->
           pure_equiv begin fun s sk fk ->
             let before,_,after = nth i (EquivSequent.get_biframe s) in
             let s =
               EquivSequent.set_biframe s (List.rev_append before after)
             in
               sk [s] fk
           end
       | _ -> raise @@ Tactics.Tactic_hard_failure
                         (Tactics.Failure "improper arguments"))

(** Tactic that succeeds (with no new subgoal) on equivalences
  * where the two frames are identical. *)
let refl (s : EquivSequent.t) sk fk =
  if EquivSequent.get_frame Term.Left s = EquivSequent.get_frame Term.Right s
  then
    sk [] fk
  else
    fk (Tactics.Failure "Frames not identical")

let () =
  T.register "refl"
    ~help:"Closes a reflexive goal.\n Usage: refl."
    (only_equiv refl)


(** For each element of the biframe, checks that it is a member of the
  * hypothesis biframe. If so, close the goal. *)
let assumption s sk fk =
  let hypothesis = EquivSequent.get_hypothesis_biframe s in
  if List.for_all (fun elem -> List.mem elem hypothesis)
      (EquivSequent.get_biframe s) then
    sk [] fk
  else
     fk (Tactics.Failure "Conclusion different from hypothesis.")

let () =
  T.register "assumption"
    ~help:"Close a goal contained in its hypothesis.\n Usage: assump."
    (only_equiv assumption)


(** Given a judgement [s] of the form H0 => E, where E is the conclusion
   biframe, and a timestamp [ts] wich does not occur inside the hypothesis
   H0, produce the judgments H0 => E{ts -> init} and E{ts->pred ts} => E.
   The second one is then direclty simplified by a case on all possible
   values of ts, producing a judgement for each one.
   It would be sound to keep the initial hypothesis H0 in all produced
   subgoals, but equivalence sequents currently support at most one
   hypothesis. *)
let induction ts s =
  let env = EquivSequent.get_env s in
  let tsubst = Theory.subst_of_env env in
  match Theory.convert tsubst ts Sorts.Timestamp with
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
      raise @@ Tactics.Tactic_soft_failure
        (Tactics.Failure "Variable should not occur in the premise");
    (* Remove ts from the sequent, as it will become unused. *)
    let s = EquivSequent.set_env (Vars.rm_var env t) s in
    let subst = [Term.ESubst (ts, Pred ts)] in
    let goal = EquivSequent.get_biframe s in
    let hypothesis = EquivSequent.(apply_subst_frame subst goal) in
    let induc_goal = EquivSequent.set_hypothesis_biframe s hypothesis in
    let init_goal =
      EquivSequent.(set_biframe
                      s (apply_subst_frame [Term.ESubst(ts,Init)] goal))
    in
    let goals = ref [] in
    (* [add_action a] adds to goals the goal corresponding to the case
     * where [t] is instantiated by [a]. *)
    let add_action a =
      let env = ref @@ EquivSequent.get_env induc_goal in
      let subst =
        List.map
          (fun i ->
             let i' = Vars.make_fresh_from_and_update env i in
             Term.ESubst (Term.Var i, Term.Var i'))
          a.Action.indices
      in
      let name = Action.to_term (Action.subst_action subst a.Action.action) in
      let ts_subst = [Term.ESubst(ts,name)] in
      goals := (EquivSequent.apply_subst ts_subst induc_goal
                |> EquivSequent.set_env !env)
               ::!goals
    in
    Action.iter_descrs (EquivSequent.get_system s) add_action ;
    init_goal::!goals
  | _  ->
    raise @@ Tactics.Tactic_soft_failure
      (Tactics.Failure "expected a timestamp variable")
  | exception (Theory.Conv _) ->
    raise @@ Tactics.Tactic_soft_failure
      (Tactics.Failure "cannot convert argument")

let () =
  T.register_general "induction"
    ~help:"Apply the induction scheme to the given timestamp.\
           \n Usage: induction t."
    (function
       | [Prover.Theory th] ->
           pure_equiv
             (fun s sk fk -> match induction th s with
                | subgoals -> sk subgoals fk
                | exception (Tactics.Tactic_soft_failure e) -> fk e)
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))


(* Enrich adds the term [t] to the judgement [s]. *)
let enrich (t : Theory.term) s sk fk =
  let tsubst = Theory.subst_of_env (EquivSequent.get_env s) in
  let elem () =
    (* Try to convert the Theory.term as either boolean or message. *)
    match Theory.convert tsubst t Sorts.Boolean with
    | f -> EquivSequent.Formula f
    | exception _ ->
      EquivSequent.Message (Theory.convert tsubst t Sorts.Message)
  in
  match elem () with
    | elem ->
      sk [EquivSequent.set_biframe s (elem :: EquivSequent.get_biframe s)] fk
    | exception _ ->
      fk Tactics.(Failure "cannot convert argument")

let () = T.register_general "enrich"
    ~help:"Enrich the goal with the given term.\
           \n Usage: enrich t."
    (function
       | [Prover.Theory v] -> pure_equiv (enrich v)
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))


(* Removes all the constant elements from the frame of [s]. *)
let const s sk fk =
  let frame = EquivSequent.get_biframe s in
  let rec is_const : type a. a Term.term -> bool = function
    | True -> true
    | False -> true
    | Fun (f,l) -> List.for_all is_const l
    | And (f,g) -> is_const f && is_const g
    | Or (f,g) -> is_const f && is_const g
    | Impl (f,g) -> is_const f && is_const g
    | Not f -> is_const f
    | _ -> false
  in
  let is_const = function
    | EquivSequent.Message e -> is_const e
    | EquivSequent.Formula e -> is_const e
  in
  sk [EquivSequent.set_biframe s
        (List.filter (fun e -> not (is_const e)) frame)] fk

let () =
  T.register "const"
    ~help:"Remove all constants from the frame.
           \n Usage: const." (pure_equiv const)


exception No_common_head
exception No_FA
let fa_expand t =
  let aux : type a. a Term.term -> EquivSequent.elem list =
    function
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
  match t with
  | EquivSequent.Message e -> aux (Term.head_normal_biterm e)
  | EquivSequent.Formula e -> aux (Term.head_normal_biterm e)

  (*| _ ->
    Tactics.soft_failure
      (Tactics.Failure "Unsupported: TODO") *)

(** Function application *)
let fa i s sk fk =
  match nth i (EquivSequent.get_biframe s) with
    | before, e, after ->
        begin try
          let biframe = List.rev_append before (fa_expand e @ after) in
          sk [EquivSequent.set_biframe s biframe] fk
          with
          | No_common_head -> fk (Tactics.Failure "No common construct")
          | No_FA -> fk (Tactics.Failure "FA not applicable")
        end
    | exception Out_of_range ->
        fk (Tactics.Failure "Out of range position")

let () =
  T.register_general "fa"
    ~help:"Break function applications on the nth term of the sequence.\
           \n Usage: fa i."
    (function
       | [Prover.Int i] -> pure_equiv (fa i)
       | _ -> Tactics.hard_failure (Tactics.Failure "Integer expected"))


let is_dup elem elems =
    if List.mem elem elems then
      true
    else
      begin
        match elem with
        (* TODO : this is unsound ! *)
        (* The matching bellow should be
        | EquivSequent.Message (
            Term.ITE(b,
            Term.Macro (im,[],l),Term.Fun(z,[]))

          ) when im = Term.in_macro && z = Term.f_zero ->
           But this raises other issues, cf #90.
        *)
        | EquivSequent.Message (Term.Macro (im,[],l))
           when im = Term.in_macro ->
          (* if the macro is an input, we check if its timestamp is lower than
             some t where frame@t of frame@pred(t) appears inside the frame *)
          let test_dup els =
            List.exists
              (function
                | EquivSequent.Message
                    (Term.Macro (fm,[],
                                 Term.Pred (Term.Action(n,is))))
                | EquivSequent.Message
                    (Term.Macro (fm,[],Term.Action(n,is)))
                  when fm = Term.frame_macro ->
                  begin
                    match l with
                    | Term.Action (n2,is2) ->
                      l = Term.Action (n,is) ||
                      Action.(depends (of_term n2 is2) (of_term n is))
                    | _ -> false
                  end
                | _ -> false)
              els
          in
          (test_dup elems)
        | _ -> false
      end

(** This function goes over all elements inside elems.  All elements that can be
   seen as duplicates, or context of duplicates, are removed. All elements that
   can be seen as context of duplicates and assumptions are removed, but
   replaced by the assumptions that appear as there subterms. *)
let rec filter_fa_dup res assump elems =
  let rec is_fa_dup acc elems e =
  (* if an element is a duplicate appearing in elems, we remove it directly *)
  if is_dup e elems then
    (true,[])
    (* if an elemnt is an assumption, we succeed, but do not remove it *)
  else if List.mem e assump then
    (true, [e])
  else
    (* else, we go recursively inside the sub-terms produced by function
       application*)
    try
      let new_els = fa_expand e in
      List.fold_left (fun (aux1,aux2) e ->
          let (fa_succ,fa_rem)= is_fa_dup acc elems e in
          fa_succ && aux1, fa_rem @ aux2
        ) (true,[]) new_els
    with No_FA | No_common_head -> (false,[])
  in
  match elems with
  | [] -> res
  | e :: els ->
    let (fa_succ,fa_rem) =  is_fa_dup [] (res@els) e in
    if fa_succ then filter_fa_dup (fa_rem@res) assump els
    else filter_fa_dup (e::res) assump els

(** This tactic filter the biframe thourgh filter_fa_dup, passing the set of
   hypothesis to it.  This is applied automatically, and essentially leaves only
   assumptions, or elements that contain a sub term which is neither a duplicate
   or an assumption.  *)
let fa_dup s sk fk =
  let biframe = EquivSequent.get_biframe s
                |> List.rev
                |> filter_fa_dup [] (EquivSequent.get_hypothesis_biframe s)
  in
  sk [EquivSequent.set_biframe s biframe] fk

let () =
  T.register_general "fadup"
    ~help:"Removes all terms that are duplicates, or context of duplicates. \
           \n Usage: fadup."
    (function
       | [] -> pure_equiv (fa_dup)
       | _ -> Tactics.hard_failure (Tactics.Failure "No parameter expected"))

(** Fresh *)

exception Name_found
exception Var_found

class find_name ~(system:Action.system) exact name = object (self)
 inherit Iter.iter_approx_macros ~exact ~system as super

  method visit_term t = match t with
    | EquivSequent.Message e -> self#visit_message e
    | EquivSequent.Formula e -> self#visit_formula e

  method visit_message t = match t with
    | Term.Name (n,_) -> if n = name then raise Name_found
    | Term.Var m -> raise Var_found
    | _ -> super#visit_message t
end

class get_name_indices ~(system:Action.system) exact name acc = object (self)
  inherit Iter.iter_approx_macros ~exact ~system as super

  val mutable indices : (Vars.index list) list = acc
  method get_indices = List.sort_uniq Pervasives.compare indices

  method visit_term t = match t with
    | EquivSequent.Message e -> self#visit_message e
    | EquivSequent.Formula e -> self#visit_formula e

  method visit_message t = match t with
    | Term.Name (n,is) -> if n = name then indices <- is::indices
    | Term.Var m -> raise Var_found
    | _ -> super#visit_message t
end

class get_actions ~(system:Action.system) exact acc = object (self)
  inherit Iter.iter_approx_macros ~exact ~system as super

  val mutable actions : Term.timestamp list = acc
  method get_actions = List.sort_uniq Pervasives.compare actions

  method visit_term t = match t with
    | EquivSequent.Message e -> self#visit_message e
    | EquivSequent.Formula e -> self#visit_formula e

  method visit_message t = match t with
    | Term.Macro (_,_,a) -> actions <- a::actions
    | _ -> super#visit_message t

  method visit_formula f = match f with
    | Term.Macro (_,_,a) -> actions <- a::actions
    | _ -> super#visit_formula f
end

(** Returns a formula expressing that vectors of indices vect_i and vect_j
  * are different (at least one component differs). *)
let mk_indices_ineq vect_i vect_j =
  List.fold_left
    (fun acc e -> Term.mk_or acc e)
    Term.False
    (List.map2 (fun i j -> Term.Atom (`Index (`Neq, i, j))) vect_i vect_j)

let mk_phi_proj system env name indices proj biframe =
  let proj_frame = List.map (EquivSequent.pi_elem proj) biframe in
  begin try
    match indices with
    | [] -> let iter_frame = new find_name ~system false name in
            List.iter iter_frame#visit_term proj_frame;
            let iter_actions = new find_name ~system false name in
            Action.(iter_descrs system
              (fun action_descr ->
                 iter_actions#visit_formula (snd action_descr.condition) ;
                 iter_actions#visit_message (snd action_descr.output) ;
                 List.iter (fun (_,t) -> iter_actions#visit_message t)
                  action_descr.updates));
            Term.True
    | _  -> let list_of_indices_from_frame =
              let iter = new get_name_indices ~system false name [] in
              List.iter iter#visit_term proj_frame ;
              iter#get_indices
            and list_of_actions_from_frame =
              let iter = new get_actions ~system false [] in
              List.iter iter#visit_term proj_frame ;
              iter#get_actions
            and tbl_of_action_indices = Hashtbl.create 10 in
            Action.(iter_descrs system
              (fun action_descr ->
                let iter = new get_name_indices ~system false name [] in
                let descr_proj = Action.pi_descr proj action_descr in
                iter#visit_formula (snd descr_proj.condition) ;
                iter#visit_message (snd descr_proj.output) ;
                List.iter (fun (_,t) -> iter#visit_message t) descr_proj.updates;
                (* we add only actions in which name occurs *)
                let action_indices = iter#get_indices in
                if List.length action_indices > 0 then
                  Hashtbl.add tbl_of_action_indices descr_proj action_indices));
            (* direct cases (for explicit occurences of name in the frame) *)
            let phi_frame =
              List.fold_left
                (fun acc f -> Term.mk_and acc f)
                Term.True
                (List.map (fun j -> mk_indices_ineq indices j) list_of_indices_from_frame)
            (* undirect cases (for occurences of name in actions of the system) *)
            and phi_actions =
              Seq.fold_left
                (fun acc f -> Term.mk_and acc f)
                Term.True
                (Seq.map
                  (* for each action in which name occurs *)
                  (fun a ->
                    let new_action_indices =
                      List.map
                        (fun i -> Vars.make_fresh_from_and_update env i)
                        a.Action.indices
                    in
                    let subst =
                      List.map2 (fun i i' -> Term.ESubst (Term.Var i,Term.Var i'))
                        a.Action.indices new_action_indices
                    in
                    let new_action = Action.to_term (Action.subst_action subst a.Action.action) in
                    (* we now apply the same substitution to the subset of
                    indices corresponding to name in the action *)
                    let new_name_indices =
                      List.map
                        (Term.subst_var subst)
                        (List.hd (Hashtbl.find tbl_of_action_indices a)) in
                    (* if new_action occurs before an action of the frame *)
                    let disj =
                      List.fold_left
                        (fun acc f -> Term.mk_or acc f)
                        Term.False
                        (List.map
                          (fun t -> Term.Atom (`Timestamp (`Leq, new_action, t)))
                          list_of_actions_from_frame)
                    (* then indices of name in new_action and of name differ *)
                    and conj = mk_indices_ineq new_name_indices indices in
                    let forall_var = List.map (fun i -> Vars.EVar i) new_action_indices in
                    Term.ForAll(forall_var,Term.Impl(disj,conj)))
                  (Hashtbl.to_seq_keys tbl_of_action_indices))
            in
            (Term.mk_and phi_frame phi_actions)
  with
  | Name_found -> raise @@ Tactics.Tactic_hard_failure
                  (Tactics.Failure "Name not fresh")
  | Var_found -> raise @@ Tactics.Tactic_hard_failure
                 (Tactics.Failure "Variable found, unsound to apply fresh")
  end

(** Returns the term if (phi_left && phi_right) then 0 else diff(nL,nR). *)
let mk_if_term system env e biframe =
  let not_name_failure = Tactics.Tactic_hard_failure
    (Tactics.Failure "Can only apply fresh tactic on names") in
  match e with
  | EquivSequent.Message t ->
      begin
      let (n_left, ind_left, n_right, ind_right) =
        match Term.pi_term true Term.Left t, Term.pi_term true Term.Right t with
        | (Name (nl,isl), Name (nr,isr)) -> (nl,isl,nr,isr)
        | _ -> raise @@ not_name_failure
      in
      let env_local = ref env in
      let system_left = Action.(make_trace_system system.left) in
      let phi_left = mk_phi_proj system_left env_local n_left ind_left Term.Left biframe in
      let system_right = Action.(make_trace_system system.right) in
      let phi_right = mk_phi_proj system_right env_local n_right ind_right Term.Right biframe in
      let then_branch = Term.Fun (Term.f_zero,[]) in
      let else_branch = t in
      match (Term.mk_and phi_left phi_right) with
      | Term.True -> EquivSequent.Message then_branch
      | phi -> EquivSequent.Message (Term.ITE(phi, then_branch, else_branch))
      end
  | EquivSequent.Formula f -> raise @@ not_name_failure

let fresh i s sk fk =
  match nth i (EquivSequent.get_biframe s) with
    | before, e, after ->
        begin try
          (* the biframe to consider when checking the freshness *)
          let biframe = List.rev_append before after in
          let system = (EquivSequent.get_system s) in
          let env = EquivSequent.get_env s in
          let if_term = mk_if_term system env e biframe in
          let biframe = (List.rev_append before (if_term::after)) in
          sk [EquivSequent.set_biframe s biframe] fk
        with
        | Tactics.Tactic_hard_failure err -> fk err
        end
    | exception Out_of_range ->
        fk (Tactics.Failure "Out of range position")

let () =
  T.register_general "fresh"
    ~help:"Removes a name if fresh.\n Usage: fresh i."
    (function
       | [Prover.Int i] -> pure_equiv (fresh i)
       | _ -> Tactics.hard_failure (Tactics.Failure "Integer expected"))

let fresh_name_ssc ~system name elems =
  begin try
    let iter = new find_name ~system false name in
    List.iter iter#visit_term elems ;
    true
  with
  | Name_found | Var_found -> false
  end

(** XOR *)
let xor i s sk fk =
  match nth i (EquivSequent.get_biframe s) with
    | before, e, after ->
        begin try
          let (name,xor_terms_left,xor_terms_right) =
            match e with
            | EquivSequent.Message Diff
                (Fun (fl,Term.Name (nl,_)::ll), Fun (fr,Term.Name (nr,_)::lr))
                when (fl = Term.f_xor && fr = Term.f_xor && nl=nr) -> (nl,ll,lr)
            | _ -> raise @@ Tactics.Tactic_hard_failure
                    (Tactics.Failure "Can only apply xor tactic on terms of the form (t1 xor t2)")
          in
          (* the biframe to consider in case of success *)
          let biframe = List.rev_append before after in
          (* the two frames to use for the freshness condition *)
          let frame_left =
            EquivSequent.Message (Fun (Term.f_xor,xor_terms_left))
            ::List.map (EquivSequent.pi_elem Term.Left) biframe in
          let frame_right =
            EquivSequent.Message (Fun (Term.f_xor,xor_terms_right))
            ::List.map (EquivSequent.pi_elem Term.Right) biframe in
          let bisystem = EquivSequent.get_system s in
          if fresh_name_ssc
               Action.(make_trace_system bisystem.left) name frame_left
          then
            if fresh_name_ssc
                 Action.(make_trace_system bisystem.right) name frame_right
            then sk [EquivSequent.set_biframe s biframe] fk
            else raise @@ Tactics.Tactic_hard_failure
              (Tactics.Failure "Name not fresh in the right system")
          else
            raise @@ Tactics.Tactic_hard_failure
              (Tactics.Failure "Name not fresh in the left system")
        with
        | Tactics.Tactic_hard_failure err -> fk err
        end
    | exception Out_of_range ->
        fk (Tactics.Failure "Out of range position")

let () =
  T.register_general "xor"
    ~help:"Removes diff(n XOR u,n XOR v) if n is fresh.\n Usage: xor i."
    (function
       | [Prover.Int i] -> pure_equiv (xor i)
       | _ -> Tactics.hard_failure (Tactics.Failure "Improper arguments"))



(* Sequence expansion of the sequence [term] for the given parameters [ths]. *)
let expand_seq (term : Theory.term) (ths:Theory.term list) (s : EquivSequent.t)
    sk fk =
  let env = EquivSequent.get_env s in
  let tsubst = Theory.subst_of_env env in
  match Theory.convert tsubst term Sorts.Message with
  (* we expect term to be a sequence *)
  | Seq ( vs, t) ->
    let vs = List.map (fun x -> Vars.EVar x) vs in
    (* we parse the arguments ths, to create a substution for variables vs *)
    let subst = Theory.parse_subst env vs ths in
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
    sk [ EquivSequent.set_biframe
           (EquivSequent.set_hypothesis_biframe s hypo_biframe)
           biframe] fk
  | _ ->
    Tactics.hard_failure
      (Tactics.Failure "Can only expand with sequences with parameters")
  | exception Theory.(Conv e) ->
      fk (Tactics.Failure  (Fmt.str "%a" Theory.pp_error e))



(* Expand all occurences of the given macro [term] inside [s] *)
let expand (term : Theory.term) (s : EquivSequent.t) sk fk =
  let tsubst = Theory.subst_of_env (EquivSequent.get_env s) in
  (* final function once the subtitustion has been computed *)
  let succ subst =
    let apply_subst = function
      | EquivSequent.Message e -> EquivSequent.Message (Term.subst subst e)
      | EquivSequent.Formula e -> EquivSequent.Formula (Term.subst subst e)
    in
    sk [EquivSequent.set_biframe s
          (List.map apply_subst (EquivSequent.get_biframe s))] fk
  in
  (* computes the substitution dependeing on the sort of term *)
  match Theory.convert tsubst term Sorts.Boolean with
    | Macro ((mn, sort, is),l,a) ->
      succ [Term.ESubst (Macro ((mn, sort, is),l,a),
                         Macros.get_definition
                           (EquivSequent.get_system s) sort mn is a)]
    | _ ->
      Tactics.hard_failure (Tactics.Failure "Can only expand macros")
    | exception Theory.(Conv (Type_error _)) ->
      begin
        match Theory.convert tsubst term Sorts.Message with
        | Macro ((mn, sort, is),l,a) ->
          succ [Term.ESubst (Macro ((mn, sort, is),l,a),
                             Macros.get_definition
                               (EquivSequent.get_system s) sort mn is a)]
        | _ ->
          Tactics.hard_failure (Tactics.Failure "Can only expand macros")
        | exception Theory.(Conv e) ->
          fk (Tactics.Failure  (Fmt.str "%a" Theory.pp_error e))
      end
    | exception Theory.(Conv e) ->
          fk (Tactics.Failure  (Fmt.str "%a" Theory.pp_error e))

let () = T.register_general "expand"
    ~help:"Expand all occurences of the given macro, or expand the given \
           sequence using the given indices.\
           \n Usage: expand macro. expand seq(i,k...->t(i,k,...),i1,k1,..."
    (function
      | [Prover.Theory v] -> pure_equiv (expand v)
      | (Prover.Theory v)::ids ->
          let ids =
            List.map
              (function
                 | Prover.Theory th -> th
                 | _ -> raise @@ Tactics.hard_failure
                     (Tactics.Failure "improper arguments"))
              ids
          in
        pure_equiv (expand_seq v ids)
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))

(** Expands all macro occurences inside the biframe, if the macro is not at some
   pred(A) but about at a concrete action. Acts recursively, also expanding the
   macros inside macro definition. *)
let expand_all s sk fk =
  let expand_all_macros t system =
    let rec aux : type a. a term -> a term = function
      | Macro ((mn, Message, is),l,_) as m
        when (mn,Sorts.Message,is) = Term.in_macro-> m
      | Macro ((mn, sort, is),l,(Action _ as a)) ->
        aux (Macros.get_definition system sort mn is a)
      | Macro ((mn, sort, is),l,(Init as a)) ->
        aux (Macros.get_definition system sort mn is a)
      | Macro ((mn, sort, is),l,_) as m -> m
      | Fun (f, l) -> Fun (f, List.map aux l)
      | Name n as a-> a
      | Var x as a -> a
      | Diff(a, b) -> Diff(aux a, aux b)
      | Left a -> Left (aux a)
      | Right a -> Left (aux a)
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
  let expand_all_macros = function
    | EquivSequent.Message e -> EquivSequent.Message (expand_all_macros e system)
    | EquivSequent.Formula e -> EquivSequent.Formula (expand_all_macros e system)
  in
  let biframe = EquivSequent.get_biframe s
                |> List.map (expand_all_macros)
  in
  sk [EquivSequent.set_biframe s biframe] fk

let () = T.register_general "expandall"
    ~help:"Expand all occurences of macros that are about explicit actions.
           \n Usage: expandall."
    (function
      | [] -> pure_equiv (expand_all)
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))


(* Replace all occurrences of [t1] by [t2] inside of [s], and asks to prove that
   t1 <=> t2. *)
let equiv t1 t2 (s : EquivSequent.t) sk fk =
  let env = EquivSequent.get_env s in
  let system = EquivSequent.get_system s in
  let tsubst = Theory.subst_of_env env in
  match Theory.convert tsubst t1 Sorts.Boolean,
        Theory.convert tsubst t2 Sorts.Boolean with
  | f1,f2 ->
    (* goal for the equivalence of t1 and t2 *)
    let trace_sequent =
        TraceSequent.init ~system
          (Term.And(Term.Impl(f1, f2), Term.Impl(f2, f1)))
          |> TraceSequent.set_env env
      in
      let subgoals =
        [ Prover.Goal.Trace trace_sequent;
          Prover.Goal.Equiv
            (EquivSequent.apply_subst [Term.ESubst(f1, f2)] s) ]
      in
      sk subgoals fk
  | exception (Theory.Conv e) ->
      Tactics.soft_failure
        (Tactics.Failure
           (Fmt.str "%a" Theory.pp_error e))

let () = T.register_general "equivalent"
    ~help:"Replace all occurences of a formula by another, and ask to prove \
           \n that they are equivalent.
           \n Usage: equiv t1, t2."
    (function
       | [Prover.Theory v1; Prover.Theory v2] -> only_equiv (equiv v1 v2)
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))

(* Reduces a conditional to its else branch, and asks to prove that its
   condition implies false. *)
let no_if i s sk fk =
  match nth i (EquivSequent.get_biframe s) with
    | before, e, after ->
      begin try
          let cond, negative_branch =
            match e with
            | EquivSequent.Message ITE (c,t,e) -> (c, EquivSequent.Message e)
            | _ -> raise @@ Tactics.Tactic_hard_failure
                (Tactics.Failure "improper arguments")
          in
          (* replace in the biframe the ite by its negative branch *)
          let biframe = List.rev_append before (negative_branch :: after) in
          let env = EquivSequent.get_env s in
          let system = EquivSequent.get_system s in
          (* ask to prove that the cond of the ite implies False *)
          let trace_sequent = TraceSequent.init ~system
              (Term.Impl(cond,False))
                                   |> TraceSequent.set_env env
           in
           sk [Prover.Goal.Trace trace_sequent;
               Prover.Goal.Equiv (EquivSequent.set_biframe s biframe)] fk
        with
          | Tactics.Tactic_soft_failure err -> fk err
        end
    | exception Out_of_range ->
        fk (Tactics.Failure "Out of range position")

let () =
  T.register_general "noif"
    ~help:"Try to prove diff equivalence by proving that the condition at the \
           \n i-th position implies False.\
           \n Usage: noif i."
    (function
       | [Prover.Int i] -> only_equiv (no_if i)
       | _ -> Tactics.hard_failure (Tactics.Failure "Integer expected"))

let yes_if i s sk fk =
 match nth i (EquivSequent.get_biframe s) with
   | before, e, after ->
     begin try
         let cond, positive_branch =
           match e with
           | EquivSequent.Message ITE (c,t,e) -> (c, EquivSequent.Message t)
           | _ -> raise @@ Tactics.Tactic_hard_failure
               (Tactics.Failure "improper arguments")
         in
         let biframe = List.rev_append before (positive_branch :: after) in
         let env = EquivSequent.get_env s in
         let system = EquivSequent.get_system s in
         let trace_sequent = TraceSequent.init ~system cond
                                  |> TraceSequent.set_env env
         in
         sk [Prover.Goal.Trace trace_sequent;
             Prover.Goal.Equiv (EquivSequent.set_biframe s biframe)] fk
       with
         | Tactics.Tactic_soft_failure err -> fk err
       end
   | exception Out_of_range ->
       fk (Tactics.Failure "Out of range position")

let () =
 T.register_general "yesif"
   ~help:"Try to prove diff equivalence by proving that the condition at the \
          \n i-th position implies True.\
          \n Usage: yesif i."
   (function
      | [Prover.Int i] -> only_equiv (yes_if i)
      | _ -> Tactics.hard_failure (Tactics.Failure "Integer expected"))

exception Not_context

class ddh_context ~(system:Action.system) exact a b c = object (self)
 inherit Iter.iter_approx_macros ~exact ~system as super

  method visit_term t = match t with
    | EquivSequent.Message e -> self#visit_message e
    | EquivSequent.Formula e -> self#visit_formula e

  method visit_macro mn is a =
    match Symbols.Macro.get_def mn with
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

class find_macros ~(system:Action.system) exact  = object (self)
 inherit Iter.iter_approx_macros ~exact ~system as super

  method visit_term t = match t with
    | EquivSequent.Message e -> self#visit_message e
    | EquivSequent.Formula e -> self#visit_formula e

  method visit_macro mn is a =
    match Symbols.Macro.get_def mn with
    | Symbols.(Input | Output | State _ | Cond | Exec | Frame) ->
      raise Macro_found
    | _ -> self#visit_macro mn is a
end


(** If all the terms of a system can be seen as a context of the terms, where
   all the names appearing inside the terms are only used inside those, returns
   true. *)
let is_ddh_context system a b c elem_list =
  let a,b,c = Symbols.Name.of_string a, Symbols.Name.of_string b, Symbols.Name.of_string c in
  let iter = new ddh_context ~system false a b c in
  let iterfm = new find_macros ~system false in
  let exists_macro =
    try
      List.iter iterfm#visit_term elem_list; false
    with Macro_found -> true
  in
  try
    (* we check that a b and c only occur in the correct form inside the system,
       if the elements contain some macro based on the system.*)
   if exists_macro then
    Action.iter_descrs system (
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
  if is_ddh_context system na nb nc
      (EquivSequent.get_biframe s) then
      sk [] fk
    else
      fk Tactics.NotDDHContext

let () = T.register_general "ddh"
    ~help:"Closes the current system, if it is an instance of a context of ddh.\
           \n Usage: ddh a, b, c."
    (function
      | [Prover.String_name v1; Prover.String_name v2;
         Prover.String_name v3] ->
        pure_equiv (ddh v1 v2 v3)
       | _ -> raise @@ Tactics.Tactic_hard_failure
           (Tactics.Failure "improper arguments"))
