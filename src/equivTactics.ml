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
    ~help:"Closes the current goal, or drop a bi-frame element.\
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
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))

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
      Tactics.soft_failure
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
    Tactics.soft_failure
      (Tactics.Failure "expected a timestamp variable")
  | exception (Theory.Conv _) ->
    Tactics.soft_failure
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
       | _ -> Tactics.hard_failure
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
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))

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

  method visit_message t = match t with
    | Term.Name (n,_) -> if n = name then raise Name_found
    | Term.Var m -> raise Var_found
    | _ -> super#visit_message t
end

class get_name_indices ~(system:Action.system) exact name = object (self)
  inherit Iter.iter_approx_macros ~exact ~system as super

  val mutable indices : (Vars.index list) list = []
  method get_indices = List.sort_uniq Pervasives.compare indices

  method visit_message t = match t with
    | Term.Name (n,is) -> if n = name then indices <- is::indices
    | Term.Var m -> raise Var_found
    | _ -> super#visit_message t
end

class get_actions ~(system:Action.system) exact = object (self)
  inherit Iter.iter_approx_macros ~exact ~system as super

  val mutable actions : Term.timestamp list = []
  method get_actions = List.sort_uniq Pervasives.compare actions

  method visit_message t = match t with
    | Term.Macro (_,_,a) -> actions <- a::actions
    | _ -> super#visit_message t

  method visit_formula f = match f with
    | Term.Macro (_,_,a) -> actions <- a::actions
    | _ -> super#visit_formula f
end

(** Construct the formula expressing freshness for some projection. *)
let mk_phi_proj system env name indices proj biframe =
  let proj_frame = List.map (EquivSequent.pi_elem proj) biframe in
  begin try
    let list_of_indices_from_frame =
      let iter = new get_name_indices ~system false name in
        List.iter iter#visit_term proj_frame ;
        iter#get_indices
    and list_of_actions_from_frame =
      let iter = new get_actions ~system false in
      List.iter iter#visit_term proj_frame ;
      iter#get_actions
    and tbl_of_action_indices = Hashtbl.create 10 in
    Action.(iter_descrs system
      (fun action_descr ->
        let iter = new get_name_indices ~system false name in
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
      List.fold_left Term.mk_and Term.True
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
        (fun a indices_a formula ->
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
                (List.sort_uniq Pervasives.compare (List.concat indices_a))
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
              Action.to_term (Action.subst_action subst a.Action.action) in
            let indices_a =
              List.map
                (List.map (Term.subst_var subst))
                indices_a in
            (* if new_action occurs before an action of the frame *)
            let disj =
              List.fold_left Term.mk_or Term.False
                (List.map
                  (fun t -> Term.Atom (`Timestamp (`Leq, new_action, t)))
                  list_of_actions_from_frame)
            (* then indices of name in new_action and of [name] differ *)
            and conj =
              List.fold_left Term.mk_and True
                (List.map
                   (fun is -> Term.mk_indices_neq is indices)
                   indices_a)
            in
            let forall_var =
              List.map (fun i -> Vars.EVar i) (new_action_indices @ bv') in
            Term.mk_and formula
              (Term.mk_forall forall_var (Term.mk_impl disj conj)))
        tbl_of_action_indices
        Term.True
    in
    Term.mk_and phi_frame phi_actions
  with
  | Name_found ->
      Tactics.soft_failure (Tactics.Failure "Name not fresh")
  | Var_found ->
      Tactics.soft_failure
        (Tactics.Failure "Variable found, unsound to apply fresh")
  end

(** Returns the term if (phi_left && phi_right) then 0 else diff(nL,nR). *)
let mk_if_term system env e biframe =
  let not_name_failure = Tactics.Tactic_soft_failure
    (Tactics.Failure "Can only apply fresh tactic on names") in
  match e with
  | EquivSequent.Message t ->
      let (n_left, ind_left, n_right, ind_right) =
        match
          Term.pi_term true Term.Left t, Term.pi_term true Term.Right t
        with
        | (Name (nl,isl), Name (nr,isr)) -> (nl,isl,nr,isr)
        | _ -> raise @@ not_name_failure
      in
      let system_left = Action.(project_system Term.Left system) in
      let phi_left =
        mk_phi_proj system_left env n_left ind_left Term.Left biframe
      in
      let system_right = Action.(project_system Term.Right system) in
      let phi_right =
        mk_phi_proj system_right env n_right ind_right Term.Right biframe
      in
      let then_branch = Term.Fun (Term.f_zero,[]) in
      let else_branch = t in
      EquivSequent.Message
        Term.(mk_ite (mk_and phi_left phi_right) then_branch else_branch)
  | EquivSequent.Formula f -> raise @@ not_name_failure

let fresh i s =
  match nth i (EquivSequent.get_biframe s) with
    | before, e, after ->
        (* the biframe to consider when checking the freshness *)
        let biframe = List.rev_append before after in
        let system = EquivSequent.get_system s in
        let env = EquivSequent.get_env s in
        let if_term = mk_if_term system env e biframe in
        let biframe = List.rev_append before (if_term::after) in
        [EquivSequent.set_biframe s biframe]
    | exception Out_of_range ->
        Tactics.soft_failure (Tactics.Failure "Out of range position")

let () =
  T.register_general "fresh"
    ~help:"Removes a name if fresh.\n Usage: fresh i."
    (function
    | [Prover.Int i] ->
        pure_equiv
          (fun s sk fk -> match fresh i s with
             | subgoals -> sk subgoals fk
             | exception (Tactics.Tactic_soft_failure e) -> fk e)
    | _ -> Tactics.hard_failure (Tactics.Failure "Integer expected"))

(* PRF axiom *)

let mk_prf_phi_proj system env param proj biframe =
  begin try
  let (hash_fn,t,key_n,key_is) = param in
  let frame =
    (EquivSequent.Message t) ::
    (List.map (EquivSequent.pi_elem proj) biframe) in
  (* check syntactic side condition *)
  Euf.prf_key_ssc ~pk:None ~system hash_fn key_n frame;
  let list_of_hashes_from_frame =
    Euf.hashes_of_frame ~system frame hash_fn key_n
  and list_of_actions_from_frame =
    let iter = new get_actions ~system false in
    List.iter iter#visit_term frame ;
    iter#get_actions
  and tbl_of_action_hashes = Hashtbl.create 10 in
  Action.(iter_descrs system
    (fun action_descr ->
      (* we add only actions in which hash occurs *)
      let descr_proj = Action.pi_descr proj action_descr in
      let action_hashes =
        Euf.hashes_of_action_descr ~system ~cond:true
          descr_proj hash_fn key_n in
      if List.length action_hashes > 0 then
        Hashtbl.add tbl_of_action_hashes descr_proj action_hashes));
  (* direct cases (for explicit occurences of hashes in the frame) *)
  let phi_frame =
    List.fold_left Term.mk_and Term.True
      (List.map
        (fun (is,m) ->
           (* select bound variables,
            * to quantify universally over them *)
           let bv =
             List.filter
               (fun i -> not (Vars.mem env (Vars.name i)))
               is
           in
           let env = ref env in
           let bv' =
             List.map (Vars.make_fresh_from_and_update env) bv in
           let subst =
             List.map2
               (fun i i' -> ESubst (Term.Var i, Term.Var i'))
               bv bv'
           in
           let is = List.map (Term.subst_var subst) is in
           Term.mk_forall
             (List.map (fun i -> Vars.EVar i) bv')
             (Term.mk_impl
               (Term.mk_indices_eq key_is is)
               (Term.Atom (`Message (`Neq, t, m)))))
        list_of_hashes_from_frame)
  (* undirect cases (for occurences of hashes in actions of the system) *)
  and phi_actions =
    Hashtbl.fold
      (fun a list_of_is_m formula ->
        (* for each action in which a hash occurs *)
          let env = ref env in
          let new_action_indices =
            List.map
              (fun i -> Vars.make_fresh_from_and_update env i)
              a.Action.indices
          in
          let bv =
            List.filter
              (fun i -> not (List.mem i a.Action.indices))
              (List.sort_uniq Pervasives.compare
                (List.concat (List.map fst list_of_is_m)))
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
            Action.to_term (Action.subst_action subst a.Action.action) in
          let list_of_is_m =
            List.map
              (fun (is,m) ->
                (List.map (Term.subst_var subst) is,Term.subst subst m))
              list_of_is_m in
          (* if new_action occurs before an action of the frame *)
          let disj =
            List.fold_left Term.mk_or Term.False
              (List.map
                (fun t -> Term.Atom (`Timestamp (`Leq, new_action, t)))
                list_of_actions_from_frame)
          (* then indices of name in new_action and of [name] differ *)
          and conj =
            List.fold_left Term.mk_and True
              (List.map
                 (fun (is,m) -> Term.mk_impl
                   (Term.mk_indices_eq key_is is)
                   (Term.Atom (`Message (`Neq, t, m))))
                 list_of_is_m)
          in
          let forall_var =
            List.map (fun i -> Vars.EVar i) (new_action_indices @ bv') in
          Term.mk_and formula
            (Term.mk_forall forall_var (Term.mk_impl disj conj)))
      tbl_of_action_hashes
      Term.True
  in
  (Term.mk_and phi_frame phi_actions)
  with
  | Euf.Bad_ssc -> raise @@ Tactics.Tactic_soft_failure
    (Tactics.Failure "Key syntactic side condition not checked")
  end

let mk_prf_if_term system env e biframe =
  let not_hash_failure = Tactics.Tactic_soft_failure
    (Tactics.Failure "PRF can only be applied on a term of the form h(t,k)") in
  match e with
  | EquivSequent.Message m ->
      let system_left = Action.(project_system Term.Left system) in
      let system_right = Action.(project_system Term.Right system) in
      let phi =
        match (Term.pi_term true Term.Left m, Term.pi_term true Term.Right m) with
        | (Term.Fun
            ((hash_fn_left, _), [t_left; Name (key_n_left,key_is_left)]),
          Term.Fun
            ((hash_fn_right, _), [t_right; Name (key_n_right,key_is_right)]))
          ->  if (Theory.is_hash hash_fn_left && Theory.is_hash hash_fn_right)
              (* FIXME handle the case diff(h(t,k),f(t1,t2)) ??? *)
              then
                let param_left =
                  (hash_fn_left,t_left,key_n_left,key_is_left) in
                let param_right =
                  (hash_fn_right,t_right,key_n_right,key_is_right) in
                Term.mk_and
                  (mk_prf_phi_proj
                    system_left env param_left Term.Left biframe)
                  (mk_prf_phi_proj
                    system_right env param_right Term.Right biframe)
              else raise @@ not_hash_failure
        | (_,
          Term.Fun
            ((hash_fn_right, _), [t_right; Name (key_n_right,key_is_right)])) ->
            if Theory.is_hash hash_fn_right then
              let param_right =
                (hash_fn_right,t_right,key_n_right,key_is_right) in
              (mk_prf_phi_proj
                system_right env param_right Term.Right biframe)
            else raise @@ not_hash_failure
        | (Term.Fun
            ((hash_fn_left, _), [t_left; Name (key_n_left,key_is_left)]),
          _) ->
            if Theory.is_hash hash_fn_left then
              let param_left =
                (hash_fn_left,t_left,key_n_left,key_is_left) in
              (mk_prf_phi_proj
                system_left env param_left Term.Left biframe)
            else raise @@ not_hash_failure
        | _ -> raise @@ not_hash_failure
      in
      let then_branch = Term.Fun (Term.f_zero,[]) in (* TODO generate fresh name *)
      let else_branch = m in
      begin
      match phi with
      | Term.True -> EquivSequent.Message then_branch
      | _ -> EquivSequent.Message (Term.ITE(phi, then_branch, else_branch))
      end
  | EquivSequent.Formula f -> raise @@ not_hash_failure

let prf i s =
  match nth i (EquivSequent.get_biframe s) with
    | before, e, after ->
        let biframe = List.rev_append before after in
        let system = (EquivSequent.get_system s) in
        let env = EquivSequent.get_env s in
        let if_term = mk_prf_if_term system env e biframe in
        let biframe = (List.rev_append before (if_term::after)) in
        [EquivSequent.set_biframe s biframe]
    | exception Out_of_range ->
        Tactics.soft_failure (Tactics.Failure "Out of range position")

let () =
 T.register_general "prf"
   ~help:"Apply the PRF axiom.\n Usage: prf i."
   (function
   | [Prover.Int i] ->
       pure_equiv
         (fun s sk fk -> match prf i s with
            | subgoals -> sk subgoals fk
            | exception (Tactics.Tactic_soft_failure e) -> fk e)
   | _ -> Tactics.hard_failure (Tactics.Failure "Integer expected"))


(** XOR *)

(* Removes the first occurence of Name (n,is) in the list l. *)
let rec remove_name_occ n is l = match l with
| [] -> []
| Name (name,indices) :: tl when (name = n && indices = is) -> tl
| hd :: tl -> hd :: (remove_name_occ n is tl)

let mk_xor_if_term system env e (opt_n : Theory.term option) biframe =
  let not_xor_failure = Tactics.Tactic_soft_failure
    (Tactics.Failure
      "Can only apply fresh tactic on terms of the form u XOR v") in
  let (n_left, is_left, l_left, n_right, is_right, l_right, term) =
    begin match opt_n with
    | None ->
      begin match e with
      | EquivSequent.Message t ->
        begin match
          Term.pi_term true Term.Left t, Term.pi_term true Term.Right t
        with
        | (Fun (fl,Term.Name (nl,isl)::ll),Fun (fr,Term.Name (nr,isr)::lr))
           when (fl = Term.f_xor && fr = Term.f_xor)
           -> (nl,isl,ll,nr,isr,lr,t)
        | _ -> raise @@ not_xor_failure
        end
      | EquivSequent.Formula f -> raise @@ not_xor_failure
      end
    | Some name ->
      let tsubst = Theory.subst_of_env env in
      begin match Theory.convert tsubst name Sorts.Message with
      | n ->
        begin match
          Term.pi_term true Term.Left n, Term.pi_term true Term.Right n
        with
        | Name (nl,isl), Name (nr,isr) ->
          begin match e with
          | EquivSequent.Message t ->
            begin match
              Term.pi_term true Term.Left t, Term.pi_term true Term.Right t
            with
            | (Fun (fl,ll),Fun (fr,lr))
              when (fl = Term.f_xor && fr = Term.f_xor)
              -> (nl,isl,remove_name_occ nl isl ll,
                  nr,isr,remove_name_occ nr isr lr,
                  t)
            | _ -> raise @@ not_xor_failure
            end
          | EquivSequent.Formula f -> raise @@ not_xor_failure
          end
        | _ -> Tactics.soft_failure (Tactics.Failure "Expected a name")
        end
      | exception (Theory.Conv _) ->
        Tactics.soft_failure
          (Tactics.Failure "Cannot convert argument")
      end
    end
  in
  let biframe =
   (EquivSequent.Message
     (Term.Diff (Fun (Term.f_xor,l_left), Fun (Term.f_xor,l_right))))
   :: biframe in
  let system_left = Action.(project_system Term.Left system) in
  let phi_left =
    mk_phi_proj system_left env n_left is_left Term.Left biframe
  in
  let system_right = Action.(project_system Term.Right system) in
  let phi_right =
    mk_phi_proj system_right env n_right is_right Term.Right biframe
  in
  let then_branch = Term.Fun (Term.f_zero,[]) in
  let else_branch = term in
  EquivSequent.Message
    Term.(mk_ite (mk_and phi_left phi_right) then_branch else_branch)

let xor i (opt_n : Theory.term option) s =
  match nth i (EquivSequent.get_biframe s) with
  | before, e, after ->
    (* the biframe to consider when checking the freshness *)
    let biframe = List.rev_append before after in
    let system = EquivSequent.get_system s in
    let env = EquivSequent.get_env s in
    let if_term = mk_xor_if_term system env e opt_n biframe in
    let biframe = List.rev_append before (if_term::after) in
    [EquivSequent.set_biframe s biframe]
  | exception Out_of_range ->
    Tactics.soft_failure (Tactics.Failure "Out of range position")

let () =
 T.register_general "xor"
   ~help:"Removes biterm (n(i0,...,ik) XOR t) if n(i0,...,ik) is fresh.
          \n Usage without giving the fresh name (should be xor's first
          argument): xor i.
          \n Usage giving the fresh name: xor i, n(i0,...,ik)."
   (function
   | [Prover.Int i] ->
       pure_equiv
         (fun s sk fk -> match xor i None s with
            | subgoals -> sk subgoals fk
            | exception (Tactics.Tactic_soft_failure e) -> fk e)
   | [Prover.Int i; Prover.Theory n] ->
       pure_equiv
         (fun s sk fk -> match xor i (Some n) s with
            | subgoals -> sk subgoals fk
            | exception (Tactics.Tactic_soft_failure e) -> fk e)
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



(* Expand all occurrences of the given macro [term] inside [s] *)
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
  ~help:"Expand all occurrences of the given macro, or expand the given \
         sequence using the given indices.\
         \n Usage: expand macro. expand seq(i,k...->t(i,k,...),i1,k1,..."
  (function
    | [Prover.Theory v] -> pure_equiv (expand v)
    | (Prover.Theory v)::ids ->
        let ids =
          List.map
            (function
               | Prover.Theory th -> th
               | _ -> Tactics.hard_failure
                        (Tactics.Failure "improper arguments"))
            ids
        in
        pure_equiv (expand_seq v ids)
     | _ ->
         Tactics.hard_failure
           (Tactics.Failure "improper arguments"))

(** Expands all macro occurrences inside the biframe, if the macro is not at
  * some pred(A) but about at a concrete action.
  * Acts recursively, also expanding the macros inside macro definition. *)
let expand_all s sk fk =
  let expand_all_macros t system =
    let rec aux : type a. a term -> a term = function
      | Macro ((mn, sort, is),l,a) when Macros.is_defined mn a ->
                aux (Macros.get_definition system sort mn is a)
      | Macro _ as m -> m
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
    ~help:"Expand all occurrences of macros that are about explicit actions.
           \n Usage: expandall."
    (function
       | [] -> pure_equiv (expand_all)
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))


(** Replace all occurrences of [t1] by [t2] inside of [s],
  * and add a subgoal to prove that [t1 <=> t2]. *)
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
          (EquivSequent.apply_subst [Term.ESubst (f1,f2)] s) ]
    in
    sk subgoals fk
  | exception (Theory.Conv e) ->
    Tactics.soft_failure
      (Tactics.Failure
         (Fmt.str "%a" Theory.pp_error e))

let () = T.register_general "equivalent"
  ~help:"Replace all occurrences of a formula by another, and ask to prove \
         \n that they are equivalent.
         \n Usage: equiv t1, t2."
  (function
     | [Prover.Theory v1; Prover.Theory v2] -> only_equiv (equiv v1 v2)
     | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))

let simplify_ite b i s =
  match nth i (EquivSequent.get_biframe s) with
  | before, e, after ->
    let cond, positive_branch, negative_branch =
      match e with
      | EquivSequent.Message ITE (c,t,e) ->
        (c, EquivSequent.Message t, EquivSequent.Message e)
      | _ -> Tactics.soft_failure (Tactics.Failure "Improper arguments")
    in
    let env = EquivSequent.get_env s in
    let system = EquivSequent.get_system s in
    if b then
      (* replace in the biframe the ite by its positive branch *)
      let biframe = List.rev_append before (positive_branch :: after) in
      (* ask to prove that the cond of the ite is True *)
      let trace_sequent = TraceSequent.init ~system cond
        |> TraceSequent.set_env env
      in
      [ Prover.Goal.Trace trace_sequent;
        Prover.Goal.Equiv (EquivSequent.set_biframe s biframe) ]
    else
      (* replace in the biframe the ite by its negative branch *)
      let biframe = List.rev_append before (negative_branch :: after) in
      (* ask to prove that the cond of the ite implies False *)
      let trace_sequent = TraceSequent.init ~system (Term.Impl(cond,False))
        |> TraceSequent.set_env env
      in
      [ Prover.Goal.Trace trace_sequent;
        Prover.Goal.Equiv (EquivSequent.set_biframe s biframe) ]
  | exception Out_of_range ->
     Tactics.soft_failure (Tactics.Failure "Out of range position")

let yes_no_if b args = match args with
  | [Prover.Int i] ->
     only_equiv
       (fun s sk fk -> match simplify_ite b i s with
         | subgoals -> sk subgoals fk
         | exception (Tactics.Tactic_soft_failure e) -> fk e)
  | _ -> Tactics.hard_failure (Tactics.Failure "Integer expected")

let () =
 T.register_general "noif"
   ~help:"Try to prove diff equivalence by proving that the condition at the \
          \n i-th position implies False.\
          \n Usage: noif i."
   (yes_no_if false)

let () =
 T.register_general "yesif"
   ~help:"Try to prove diff equivalence by proving that the condition at the \
          \n i-th position is True.\
          \n Usage: yesif i."
   (yes_no_if true)

exception Not_context

class ddh_context ~(system:Action.system) exact a b c = object (self)
 inherit Iter.iter_approx_macros ~exact ~system as super

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
       | [Prover.String_name v1;
          Prover.String_name v2;
          Prover.String_name v3] ->
         pure_equiv (ddh v1 v2 v3)
       | _ -> Tactics.hard_failure (Tactics.Failure "improper arguments"))
