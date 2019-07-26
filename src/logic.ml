open Utils
open Action
open Term

(** Tags used to record some information on gamma elements:
    - [trs] records whether it is included in the last completion.
    - [euf] records whether the EUF axiom has been applied. *)
type tag = { t_trs : bool;
             t_euf : bool }

let new_tag () = { t_trs = false; t_euf = false }

let set_trs b t = { t with t_trs = b }

let set_euf b t = { t with t_euf = b }


module Gamma : sig
  (** Type of judgment contexts. *)
  type gamma

  val mk : unit -> gamma

  val add_fact : gamma -> fact -> gamma
  val add_facts : gamma -> fact list -> gamma

  val get_facts : gamma -> fact list
  val set_facts : gamma -> fact list -> gamma

  val complete : gamma -> gamma option

  val select : gamma -> (atom -> tag -> bool) -> (tag -> tag) -> gamma * atom
end = struct
  (** Type of judgment contexts. We separate atoms from more complexe facts.
      We store in [trs] the state of the completion algorithm when it was last
      called on [atoms]. *)
  type gamma = { facts : fact list;
                 atoms : (atom * tag) list;
                 trs : Completion.state option }

  let mk () = { facts = []; atoms = []; trs = None }

  (** We do not add atoms that are already a consequence of gamma. *)
  let add_atom g at =
    let add at =  { g with atoms = (at, new_tag ()) :: g.atoms } in
    if g.trs = None then add at else
      match at with
      | (Eq,s,t) ->
        if Completion.check_equalities (opt_get g.trs) [s,t] then g
        else add at
      | (Neq,s,t) ->
        if Completion.check_disequalities (opt_get g.trs) [s,t] then g
        else add at
      | _ -> add at (* TODO: do not add useless inequality atoms *)

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

  let get_facts g = g.facts

  let set_facts g fs = add_facts { g with facts = [] } fs

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
      Utils.some { g with trs = Some trs;
                          atoms = List.map (fun (at,t) ->
                              ( at, set_trs false t )
                            ) g.atoms }
    else None

  (** [select g f f_up] returns the pair [(g',at)] where [at] is such that
      [f at tag] is true (where [tag] is the tag of [at] in [g]), and [at]'s
      tag has been updated in [g] according to [f_up].
      Raise [Not_found] if no such element exists. *)
  let select g f f_up =
    let rec aux acc = function
      | [] -> raise Not_found
      | (at, t) :: rem ->
        if f at t then
          ({ g with atoms = List.rev_append acc ((at, f_up t) :: rem) }, at)
        else aux ((at,t) :: acc) rem in

    aux [] g.atoms

end

(** Allow to store constraint. We remember the last models that was computed,
    potentially on a less restricted constraint.
    We should guarrantee that TODO (give the invariant on models and queries) *)
module Theta : sig
  type theta

  val mk : constr -> theta

  val add_constr : theta -> constr -> theta

  val is_sat : theta -> bool

  (** [maximal_elems theta elems] returns an over-approximation of the set of
      maximals elements of [elems] in [theta]. *)
  val maximal_elems : theta -> timestamp list -> timestamp list
end = struct
  open Constr

  type theta = { constr : constr;
                 models : models option ref;
                 models_is_exact : bool ref }

  let mk constr = { constr = constr;
                    models = ref None;
                    models_is_exact = ref false }

  let add_constr theta c = { theta with constr = And(theta.constr, c);
                                        models_is_exact = ref false }

  let compute_models theta =
    if !(theta.models_is_exact) then ()
    else begin
      let models = Constr.models theta.constr in
      theta.models := Some models;
      theta.models_is_exact := true end

  let is_sat theta =
    compute_models theta;
    Constr.m_is_sat (opt_get !(theta.models))

  let maximal_elems theta tss =
    compute_models theta;
    Constr.maximal_elems (opt_get !(theta.models)) tss
end

(** Type of judgments:
    - [environment] contains the current protocol declaration.
      For now, this is [Euf.process] but should be changed (TODO).
    - [vars] and [indices] are the judgment free timestamp and index variables.
    - [theta.constr] constrains the judgment timestamp and index variables.
    - [theta.models] store the last minimal models of [theta.constr].
    - [gamma] is the judgment context.
    - [goal] contains the current goal, which is of type 'a.  *)
type 'a judgment = { environment : Euf.process;
                     vars : tvar list;
                     indices: Action.indices;
                     theta : Theta.theta;
                     gamma : Gamma.gamma;
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
       theta =
         Theta.add_constr
           judge.theta
           (subst_constr iv_subst tv_subst judge.goal.uconstr);

       gamma = subst_fact iv_subst tv_subst judge.goal.ufact
               |> Gamma.add_fact judge.gamma;

       goal = List.map (fun goal ->
           subst_postcond iv_subst tv_subst goal
         ) judge.goal.postcond }
    fk

(** [goal_exists_intro judge sk fk vnu inu] introduces the existentially
    quantified variables and the goal, assuming the constraint on the
    existential variables is satisfied (if [force] is true, then the
    introduction is done even is the constraint is not satisfied by updating
    the judgment constraint.
    [vnu] (resp. [inu]) is a mapping from the postcondition existentially binded
    timestamp (resp. index) variables to [judge.gamma] timestamp (resp. index)
    variables. *)
let goal_exists_intro (judge : postcond judgment) sk fk ?force:(f=false) vnu inu =
  let pc_constr = subst_constr inu vnu judge.goal.econstr in

  (* We check whether [judge.theta.constr] implies [pc_constr].
     Equivalently, we could check whether:
     (Impl (judge.theta.constr,pc_constr)) is satisifable
     But [pc_constr] should be usually smaller than [judge.theta], and
     therefore it is better to negate [pc_constr], as this yields smaller
     formula when we put the constraint in DNF. *)
  let theta' = Theta.add_constr judge.theta (Not pc_constr) in
  if not @@ Theta.is_sat theta' then
    sk { judge with goal = subst_postcond inu vnu judge.goal }
      fk
  else if f then
    sk { judge with goal = subst_postcond inu vnu judge.goal;
                    theta = theta' }
      fk
  else fk ()

let goal_intro (judge : fact judgment) sk fk =
  sk { judge with gamma = Gamma.add_fact judge.gamma (Not judge.goal);
                  goal = False } fk

let fail_goal_false (judge : fact judgment) sk fk = match judge.goal with
  | False -> fk ()
  | _ -> raise @@ Failure "goal ill-formed"

let constr_absurd (judge : 'a judgment) sk fk =
  if not @@ Theta.is_sat judge.theta then sk () fk else fk ()

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
  let sel, nsel = List.split_pred select_pred (Gamma.get_facts judge.gamma) in

  let rec mk_facts acc = function
    | [] -> [acc]
    | l :: ors -> List.map (fun x -> mk_facts (x :: acc) ors) l
                  |> List.flatten in

  let judges =
    mk_facts [] (List.map or_to_list sel)
    |> List.map (fun fs ->
        { judge with gamma = Gamma.set_facts judge.gamma (fs @ nsel) } ) in

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

let euf_apply_case theta (_, (_, key_is), m, s) case =
  let open Euf in
  let open Process in
  (* We create fresh indices to rename in the block *)
  let inu = List.map (fun i -> (i, fresh_index ())) case.blk_descr.indices in
  (* We create a fresh timestamp variable rename in the block. *)
  let vnu = [] in

  (* We create the block hashed message. *)
  let blk_m = subst_term inu vnu case.message in

  (* We create the term equality *)
  let eq = Atom (Eq, blk_m, m) in
  let new_f = And (eq, subst_fact inu vnu case.blk_descr.condition) in

  (* Now, we need to add the timestamp constraints. *)

  (* The block action name and the block timestamp variable are equal. *)
  let blk_ts = TName case.blk_descr.action in

  (* The block occured before the test H(m,k) = s. *)
  let le_cnstr =
    List.map (fun ts ->
        Atom (Pts (Leq, blk_ts, ts))
      ) (Theta.maximal_elems theta (term_ts s @ term_ts m))
    |> mk_or_cnstr in

  (* The key indices in the bock and when m was hashed are the same. *)
  let eq_cnstr =
    List.map2 (fun i i' ->
        Atom (Pind (Eq, i, i'))
      ) key_is case.key_indices
    |> mk_and_cnstr in

  let constr = And (eq_cnstr, le_cnstr) in

  (new_f, constr)


let euf_apply_facts judge at = match modulo_sym euf_param at with
  | None -> raise @@ Failure "bad euf application"
  | Some p ->
    let (hash_fn, (key_n, key_is), m, s) = p in
    let rule = Euf.mk_rule judge.environment hash_fn key_n in
    List.map (fun case ->
        let new_f, new_cnstr = euf_apply_case judge.theta p case in
        { judge with theta = Theta.add_constr judge.theta new_cnstr;
                     gamma = Gamma.add_fact judge.gamma new_f }
      ) rule.Euf.cases

let euf_apply (judge : 'a judgment) sk fk f_select =
  let g, at = Gamma.select judge.gamma f_select (set_euf true) in
  let judge = { judge with gamma = g } in

  (* TODO: need to add block equalities somewhere. *)
  sk (euf_apply_facts judge at) fk



(* let () =
 *   Checks.add_suite "Logic" [
 *     "Empty", `Quick,
 *     begin fun () -> ()
 *     end
 *   ] *)
