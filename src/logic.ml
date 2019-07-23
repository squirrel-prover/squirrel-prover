open Utils
open Term
open Constr

module Gamma = struct
  (** Tags used to record some information on gamma elements:
      - [trs] records whether it is included in the last completion.
      - [euf] records whether the EUF axiom has been applied. *)
  type tag = { t_trs : bool;
               t_euf : bool }

  (** Type of judgment contexts. We separate atoms from more complexe facts.
      We store in [trs] the state of the completion algorithm when it was last
      called *)
  type gamma = { facts : fact list;
                 atoms : (atom * tag) list;
                 trs : Completion.state }

  let get_el (at,_) = at
  let get_tag (_,tag) = tag

  let new_tag () = { t_trs = false; t_euf = false }

  let set_trs b (x, t) = (x, { t with t_trs = b })

  let set_euf b (x, t) = (x, { t with t_euf = b })

  (** We remove atoms that are already a consequence of gamma. *)
  let add_atom g at =
    let add at =  { g with atoms = (at, new_tag ()) :: g.atoms } in

    match at with
    | (Eq,s,t) ->
      if Completion.check_equalities g.trs [s,t] then g else add at
    | (Neq,s,t) ->
      if Completion.check_disequalities g.trs [s,t] then g else add at
    | _ -> add at                 (* TODO: do not add useless inequality atoms *)

  let rec add_atoms g = function
    | [] -> g
    | at :: ats -> add_atoms (add_atom g at) ats

  (** [add_fact g f] adds [f] to [g]. We try some trivial simplification. *)
  let rec add_fact g = function
    | Atom at -> add_atom g at
    | Not (Atom at) ->  add_atom g (not_xpred at)
    | True -> g
    | And (f,f') -> add_fact (add_fact g f) f'
    | _ as f -> { g with facts = f :: g.facts }

  let rec add_facts g = function
    | [] -> g
    | f :: fs -> add_facts (add_fact g f) fs

  (** [complete_gamma g] returns [None] if [g] is inconsistent, and [Some g']
      otherwise, where [g'] has been completed. *)
  let complete g =
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
end

module Theta = struct

  type theta = { constrs : constr list;
                 tatoms : tatom list;
               }

end

open Gamma
open Theta

(** Type of judgments:
    - [environment] contains the current protocol declaration.
      For now, this is [Euf.process] but should be changed (TODO).
    - [vars] and [indices] are the judgment free timestamp and index variables.
    - [constr] constrains the judgment timestamp and index variables.
    - [gamma] is the judgment context.
    - [goal] contains the current goal, which is of type 'a.  *)
type 'a judgment = { environment : Euf.process;
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


type ('a,'b) mem_fk = 'a -> 'b

type ('a,'b,'c) mem_sk = 'a -> ('b,'c) mem_fk -> 'c

type ('a,'b,'c,'d) mem_t = 'a -> ('b,'c,'d) mem_sk -> ('c,'d) mem_fk -> 'd


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


(** Introduce the universally quantified variables and the goal. *)
let goal_forall_intro (judge : formula judgment) sk fk =
  let compute_alpha ffresh l l' =
    List.fold_left (fun subst x ->
        if List.mem x l' then (x, ffresh ()) :: subst else subst
      ) [] l in

  let tv_subst = compute_alpha fresh_tvar judge.goal.uvars judge.vars
  and iv_subst = compute_alpha fresh_index judge.goal.uindices judge.indices in

  sk { judge with
       constr = And ( judge.constr,
                      subst_constr iv_subst tv_subst judge.goal.uconstr);

       gamma = subst_fact iv_subst tv_subst judge.goal.ufact
               |> add_fact judge.gamma;

       goal = List.map (fun goal ->
           subst_postcond iv_subst tv_subst goal
         ) judge.goal.postcond }
    fk

(** [goal_exists_intro judge sk fk vnu inu] introduces the existentially
    quantified variables and the goal, assuming the constraint on the
    existential variables is satisfied (if [force] is true, then the introduction
    is done even is the constraint is not satisfied by updating the judgment
    constraint.
    [vnu] (resp. [inu]) is a mapping from the postcondition existentially binded
    timestamp (resp. index) variables to [judge.gamma] timestamp (resp. index)
    variables. *)
let goal_exists_intro (judge : postcond judgment) sk fk ?force:(f=false) vnu inu =
  let pc_constr = subst_constr inu vnu judge.constr in

  if Constr.is_sat (Impl (judge.constr,pc_constr)) then
    sk { judge with goal = subst_postcond inu vnu judge.goal }
      fk
  else if f then
    sk { judge with goal = subst_postcond inu vnu judge.goal;
                    constr = And (judge.constr, Not pc_constr) }
      fk
  else fk ()

let goal_intro (judge : fact judgment) sk fk =
  sk { judge with gamma = add_fact judge.gamma (Not judge.goal);
                  goal = False } fk

let fail_goal_false (judge : fact judgment) sk fk = match judge.goal with
  | False -> fk ()
  | _ -> raise @@ Failure "goal ill-formed"

let constr_absurd (judge : 'a judgment) sk fk =
  let models = Constr.models judge.constr in
  if not @@ Constr.m_is_sat models then sk () fk else fk ()

(** In case of failure, we pass the judgement with the completed gamma to the
    failure continuation. *)
let gamma_absurd (judge : 'a judgment) msk mfk =
  match Gamma.complete judge.gamma with
  | None -> msk () mfk
  | Some g' -> mfk g'


let or_to_list f =
  let rec aux acc = function
    | Or (g,h) -> aux (aux acc g) h
    | _ as a -> a :: acc in

  (* Remark that we simplify the formula. *)
  aux [] (simpl_fact f)

let gamma_or_intro (judge : 'a judgment) sk fk select_pred =
  let sel, nsel = List.split_pred select_pred judge.gamma.facts in

  let rec mk_facts acc = function
    | [] -> [acc]
    | l :: ors -> List.map (fun x -> mk_facts (x :: acc) ors) l
                  |> List.flatten in

  let judges =
    mk_facts [] (List.map or_to_list sel)
    |> List.map (fun fs ->
        { judge with
          gamma = add_facts { judge.gamma with facts = nsel } fs
        } ) in

  sk judges fk


let rec prove_all (judges : 'a judgment list) sk sk_end fk = match judges with
  | [] -> sk_end () fk
  | j :: judges' ->
    sk j fk;
    prove_all judges sk sk_end fk


(* TODO: add a new block equalities *)
let add_block _ = assert false

(** EUF Axiom *)

(** [modulo_sym f at] applies [f] to [at] modulo symmetry of the equality. *)
let modulo_sym f at = match at with
  | (Eq as ord,t1,t2) | (Neq as ord,t1,t2) -> begin match f at with
      | Some _ as res -> res
      | None -> f (ord,t2,t1) end
  | _ -> f at

let euf_param (at : atom) = match at with
  | (Eq, Fun ((hash,_), [m; Name key]), s) ->
    if Theory.is_hash hash then
      Some (hash,key,m,s)
    else None
  | _ -> None

let mk_or_cnstr l = match l with
  | [] -> raise @@ Failure "empty list"
  | [a] -> a
  | a :: l' ->
    let rec mk_c acc = function
      | [] -> acc
      | x :: l -> mk_c (Or (x,acc)) l in

    mk_c a l'

let mk_and_cnstr l = match l with
  | [] -> raise @@ Failure "empty list"
  | [a] -> a
  | a :: l' ->
    let rec mk_c acc = function
      | [] -> acc
      | x :: l -> mk_c (And (x,acc)) l in

    mk_c a l'

let euf_apply_case (_, (_, key_is), m, s) case =
  let open Euf in
  (* We create fresh indices to rename in the block *)
  let inu = List.map (fun i -> (i, fresh_index ())) case.block.binded_indices in
  (* We create a fresh timestamp variable rename in the block. *)
  let fresh_ts = fresh_tvar () in
  let vnu = [case.block.ts, fresh_ts] in

  (* We create the block hashed message. *)
  let blk_m = subst_term inu vnu case.message in
  (* We create the term equality *)
  let eq = Atom (Eq, blk_m, m) in
  let new_f = And (eq, subst_fact inu vnu case.block.condition) in

  (* Now, we need to add the timestamp constraints. *)

  (* The block action name and the block timestamp variable are equal. *)
  let blk_ts = TName (case.block.action, List.map snd inu) in
  let ts_eq = Atom (Pts (Eq, TVar fresh_ts, blk_ts)) in

  (* The block occured before the test H(m,k) = s. *)
  (* TODO: this is brutal, because we are using a Or, and are not simplifying
     the list of timestampts by keeping only the maximal elements. *)
  let le_cnstr =
    List.map (fun ts ->
        Atom (Pts (Leq, blk_ts, ts))
      ) (term_ts s @ term_ts m)
    |> mk_or_cnstr in

  (* The key indices in the bock and when m was hashed are the same. *)
  let eq_cnstr =
    List.map2 (fun i i' ->
        Atom (Pind (Eq, i, i'))
      ) key_is case.key_indices
    |> mk_and_cnstr in

  let constr = And (ts_eq, And (eq_cnstr, le_cnstr)) in

  (new_f, constr)


let euf_apply_facts judge at = match modulo_sym euf_param at with
  | None -> raise @@ Failure "bad euf application"
  | Some p ->
    let (hash_fn, (key_n, key_is), m, s) = p in
    let rule = Euf.mk_rule judge.environment hash_fn key_n in
    List.map (fun case ->
        let new_f, new_cnstr = euf_apply_case p case in
        { judge with constr = And (judge.constr, new_cnstr);
                     gamma = add_fact judge.gamma new_f }
      ) rule.Euf.cases

let euf_apply (judge : 'a judgment) sk fk select =
  let t_at, ats = select judge.gamma in
  let judge = { judge with
                gamma = { judge.gamma with
                          atoms = (set_euf true t_at) :: ats } } in

  (* TODO: need to add block equalities somewhere. *)
  sk (euf_apply_facts judge (get_el t_at)) fk



(* let () =
 *   Checks.add_suite "Logic" [
 *     "Empty", `Quick,
 *     begin fun () -> ()
 *     end
 *   ] *)
