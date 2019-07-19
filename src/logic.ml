open Term
open Constr


(** Tags used to record some information on gamma elements:
    - [trs] records whether it is included in the last completion.
    - [euf] records whether the EUF axiom has been applied. *)
type tag = { t_trs : bool;
             t_euf : bool }

(** Type of judgment contexts. We separate atoms from more complexe facts.
    We store in [trs] the state of the completion algorithm when it was last
    called *)
type gamma = { facts : (fact * tag) list;
               atoms : (atom * tag) list;
               trs : Completion.state }

let new_tag () = { t_trs = false; t_euf = false }

let set_trs b (x, t) = (x, { t with t_trs = b })

(** We remove atoms that are already a consequence of gamma. *)
let add_atom g at =
  let add at =  { g with atoms = (at, new_tag ()) :: g.atoms } in

  match at with
  | (Eq,s,t) ->
    if Completion.check_equalities g.trs [s,t] then g else add at
  | (Neq,s,t) ->
    if Completion.check_disequalities g.trs [s,t] then g else add at
  | _ -> add at                 (* TODO: do not add useless inequality atoms *)

(** [add_fact g f] adds [f] to [g]. We try some trivial simplification. *)
let rec add_fact g = function
  | Atom at -> add_atom g at
  | Not (Atom at) ->  add_atom g (not_xpred at)
  | True -> g
  | And (f,f') -> add_fact (add_fact g f) f'
  | _ as f -> { g with facts = (f, new_tag ()) :: g.facts }

(** [complete_gamma g] returns [None] if [g] is inconsistent, and [Some g']
    otherwise, where [g'] has been completed. *)
let complete_gamma g =
  let eqs, _, neqs = List.map fst g.atoms
                        |> List.map norm_xatom
                        |> List.flatten
                        |> List.fold_left (fun acc (od,a,b) ->
                            add_xeq od (a,b) acc) ([],[],[]) in

  (* TODO: for now, we ignore inequalities *)
  let trs = Completion.complete eqs in
  if Completion.check_disequalities trs neqs then
    Utils.some { g with trs = trs;
                        atoms = List.map (set_trs false) g.atoms }
  else None

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

let constr_absurd (judge : 'a judgment) sk fk =
  if not @@ Constr.is_sat judge.constr then sk () else fk ()

let gamma_absurd (judge : 'a judgment) sk fk =
  match complete_gamma judge.gamma with
  | None -> sk ()
  | Some _ -> fk ()


(* Utils *)

(** [modulo_sym f at] applies [f] to [at] modulo symmetry of the equality. *)
let modulo_sym f at = match at with
  | (Eq as ord,t1,t2) | (Neq as ord,t1,t2) -> begin match f at with
      | Some _ as res -> res
      | None -> f (ord,t2,t1) end
  | _ -> f at
