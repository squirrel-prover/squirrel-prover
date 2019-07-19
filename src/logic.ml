open Term
open Constr

(** Type of judgment contexts. We separate facts that have already been treated
    from those that have not.
    Moreover, we store in [trs] the state of the completion algorithm when it was
    called on [old_facts]. *)
type gamma = { old_facts : fact list;
               new_facts : fact list;
               trs : Completion.state }


let add_fact gamma fact = { gamma with new_facts = fact :: gamma.new_facts }


(** Type of judgments:
    - [environment] contains the current protocol declaration (TODO).
    - [vars] and [indices] are the judgment free timestamp and index variables.
    - [constr] constrains the judgment timestamp and index variables.
    - [gamma] is the judgment context.
    - [goal] contains the current goal, which is of type 'a.  *)
type 'a judgment = { environment : unit;
                     vars : tvar list;
                     indices: indices;
                     constr : constr;
                     gamma : gamma;
                     goal : 'a }


(***********)
(* Tactics *)
(***********)

type 'a fk = unit -> 'a

type ('a,'b) sk = 'a -> 'b fk -> 'b

type ('a,'b,'c) t = 'a -> ('b,'c) sk -> 'c fk -> 'c

let tact_wrap f v sk fk = sk (f v) fk

let tact_return a v = a v (fun r fk' -> r) (fun _ -> raise @@ Failure "return")

let tact_andthen a b sk fk v = a v (fun v fk' -> b v sk fk') fk

let tact_or a b sk fk v = a v sk (fun () -> b v sk fk)


(**********************)
(* Introduction Rules *)
(**********************)

let goal_or_intro_l (judge : fact judgment) sk fk = match judge.goal with
  | Or (lgoal, _) -> sk { judge with goal = lgoal } fk
  | _ -> raise @@ Failure "goal ill-formed"

let goal_or_intro_r (judge : fact judgment) sk fk = match judge.goal with
  | Or (_, rgoal) -> sk { judge with goal = rgoal } fk
  | _ -> raise @@ Failure "goal ill-formed"

(** To prove phi \/ psi, try first to prove phi and then psi *)
let goal_or_intro (judge : fact judgment) sk fk =
  tact_or goal_or_intro_l goal_or_intro_r sk fk judge

let goal_true_intro (judge : fact judgment) sk fk = match judge.goal with
  | True -> sk () fk
  | _ -> raise @@ Failure "goal ill-formed"

let goal_and_intro (judge : fact judgment) sk fk = match judge.goal with
  | And (lgoal,rgoal) ->
    sk { judge with goal = lgoal } fk;
    sk { judge with goal = rgoal } fk;

  | _ -> raise @@ Failure "goal ill-formed"


(** Introduce the universally quantified variables and the precondition. *)
let goal_forall_intro (judge : formula judgment) sk fk =
  let compute_alpha ffresh l l' =
    List.fold_left (fun subst x ->
        if List.mem x l' then (x, ffresh ()) :: subst else subst
      ) [] l in

  let tv_subst = compute_alpha fresh_tvar judge.goal.uvars judge.vars
  and iv_subst = compute_alpha fresh_index judge.goal.uindices judge.indices in

  { judge with constr = And ( judge.constr,
                              ivar_subst_constr iv_subst judge.goal.uconstr
                              |> tvar_subst_constr tv_subst );

               gamma = ivar_subst_fact iv_subst judge.goal.ufact
                       |> tvar_subst_fact tv_subst
                       |> add_fact judge.gamma;

               goal = List.map (fun goal ->
                   ivar_subst_postcond iv_subst goal
                   |> tvar_subst_postcond tv_subst
                 ) judge.goal.postcond }


let fail_goal_false (judge : fact judgment) sk fk = match judge.goal with
  | False -> fk ()
  | _ -> raise @@ Failure "goal ill-formed"
