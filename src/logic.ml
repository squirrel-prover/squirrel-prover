open Utils
open Action
open Term

type args = (string * Theory.kind) list

let goals = ref []

let iter_goals f = List.iter f !goals

let add_goal g = goals := g :: !goals


let declare_goal (uargs,uconstr) (eargs,econstr) ufact efact =
  let to_ts subst = List.map (fun (x,y) -> x, Term.TVar y) subst in

  (* In the rest of this function, the lists need to be reversed and appended
     carefully to properly handle variable shadowing.  *)
  let uts_subst, uindex_subst = Theory.convert_vars uargs
  and ets_subst, eindex_subst = Theory.convert_vars eargs in

  let uconstr =
    Theory.convert_constr_glob
      (List.rev uargs)
      (to_ts uts_subst)
      uindex_subst
      uconstr in
  let ufact =
    Theory.convert_fact_glob
      (to_ts uts_subst)
      uindex_subst
      ufact in

  let econstr =
    Theory.convert_constr_glob
      (List.rev_append eargs (List.rev uargs))
      (to_ts ets_subst @ to_ts uts_subst)
      (eindex_subst @ uindex_subst)
      econstr in
  let efact =
    Theory.convert_fact_glob
      (to_ts ets_subst @ to_ts uts_subst)
      (eindex_subst @ uindex_subst)
      efact in

  add_goal
    { uvars = List.map snd uts_subst;
      uindices = List.map snd uindex_subst;
      uconstr = uconstr;
      ufact = ufact;
      postcond = [{ evars = List.map snd ets_subst;
                    eindices = List.map snd eindex_subst;
                    econstr = econstr;
                    efact = efact }]
    }



let rec action_of_ts = function
  | TName a -> Some a
  | TPred ts -> action_of_ts ts
  | TVar _ -> None

(** Tags used to record some information on gamma elements:
    - [euf] records whether the EUF axiom has been applied. *)
type tag = { t_euf : bool }

let new_tag () = { t_euf = false }

let set_euf b t = { t_euf = b }


module Gamma : sig
  (** Type of judgment contexts. *)
  type gamma

  val pp_gamma : Format.formatter -> gamma -> unit

  val mk : unit -> gamma

  val add_fact : gamma -> fact -> gamma
  val add_facts : gamma -> fact list -> gamma

  val get_facts : gamma -> fact list
  val set_facts : gamma -> fact list -> gamma

  val get_atoms : gamma -> atom list

  val get_trs : gamma -> Completion.state

  val is_sat : gamma -> bool

  val select : gamma -> (atom -> tag -> bool) -> (tag -> tag) -> gamma * atom

  val add_descr : gamma -> Process.descr -> gamma
end = struct
  (** Type of judgment contexts. We separate atoms from more complexe facts.
      We store in [trs] the state of the completion algorithm when it was last
      called on [atoms]. *)
  type gamma = { facts : fact list;
                 atoms : (atom * tag) list;
                 trs : Completion.state option ref;
                 actions_described : Action.action list }

  let pp_gamma ppf gamma =
    Fmt.pf ppf "@[<v 0>\
                @[<hov 2>Actions described:@ %a@]@;\
                @[<hv 2>Facts:@ @[<v 0>%a@]@]@;\
                @[<hv 2>Atoms:@ @[<v 0>%a@]@]@;@]"
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") Action.pp_action)
      gamma.actions_described
      (Fmt.list Term.pp_fact) gamma.facts
      (Fmt.list (fun ppf (at,_) -> Term.pp_atom ppf at)) gamma.atoms

  let mk () = { facts = []; atoms = []; trs = ref None; actions_described = [] }

  (** We do not add atoms that are already a consequence of gamma. *)
  let add_atom g at =
    let add at =  { g with atoms = (at, new_tag ()) :: g.atoms } in
    if !(g.trs) = None then add at else
      match at with
      | (Eq,s,t) ->
        if Completion.check_equalities (opt_get !(g.trs)) [s,t] then g
        else add at
      | (Neq,s,t) ->
        if Completion.check_disequalities (opt_get !(g.trs)) [s,t] then g
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

  let get_atoms g = List.map fst g.atoms

  let get_trs g = match !(g.trs) with Some x -> x | None -> raise Not_found

  (** [complete_gamma g] returns [None] if [g] is inconsistent, and [Some g']
      otherwise, where [g'] has been completed. *)
  let is_sat g =
    let eqs, _, neqs = List.map fst g.atoms
                       |> List.map norm_xatom
                       |> List.flatten
                       |> List.fold_left (fun acc (od,a,b) ->
                           add_xeq od (a,b) acc) ([],[],[]) in

    (* TODO: for now, we ignore inequalities *)
    let trs = Completion.complete eqs in
    if Completion.check_disequalities trs neqs then
      let () = g.trs := Some trs in true
    else false

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

  let rec add_descr g d =
    let open Process in
    if List.mem d.action g.actions_described then g
    else
      let g =  { g with actions_described = d.action :: g.actions_described } in
      let new_atoms =
        (Eq, Macro (out_macro, TName d.action), d.output)
        :: List.map (fun (s,t) ->
            (Eq, State (s, TName d.action), t)
          ) d.updates in

      (* We recursively add necessary descriptions. *)
      let actions = Term.atoms_ts new_atoms
                    |> List.fold_left (fun acc ts -> match action_of_ts ts with
                        | None -> acc
                        | Some a -> a :: acc
                      ) [] in

      let descrs = List.map Process.get_descr actions in
      let g = List.fold_left add_descr g descrs in

      add_atoms g new_atoms
end

(** Store the constraints. We remember the last models that was computed,
    potentially on a less restricted constraint.
    We should guarrantee that TODO (give the invariant on models and queries) *)
module Theta : sig
  type theta

  val pp_theta : Format.formatter -> theta -> unit

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

  let pp_theta ppf theta = Term.pp_constr ppf theta.constr

  let mk constr = { constr = constr;
                    models = ref None;
                    models_is_exact = ref false }

  let add_constr theta c =
    { theta with constr = Term.triv_eval (And(theta.constr, c));
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

module Judgment : sig
  (** Type of judgments:
      - [vars] and [indices] are the judgment free timestamp and index variables.
      - [theta.constr] constrains the judgment timestamp and index variables.
      - [theta.models] store the last minimal models of [theta.constr].
      - [gamma] is the judgment context.
      - [goal] contains the current goal, which is of type 'a. *)
  type 'a judgment = private { vars : tvar list;
                               indices: Action.indices;
                               theta : Theta.theta;
                               gamma : Gamma.gamma;
                               goal : 'a }

  val pp_judgment :
    (Format.formatter -> 'a -> unit) ->
    Format.formatter ->
    'a judgment ->
    unit

  val init : formula -> formula judgment

  val add_vars : Term.tvar list -> 'a judgment -> 'a judgment
  val add_indices : Action.indices -> 'a judgment -> 'a judgment

  (** Side-effect: Add necessary action descriptions. *)
  val add_fact : Term.fact -> 'a judgment -> 'a judgment

  (** Side-effect: Add necessary action descriptions. *)
  val add_constr : Term.constr -> 'a judgment -> 'a judgment

  (** Side-effect: Add necessary action descriptions. *)
  val set_goal_fact : fact -> 'a judgment -> fact judgment

  val set_goal : 'b -> 'a judgment -> 'b judgment

  val set_gamma : Gamma.gamma -> 'a judgment ->  'a judgment
end = struct
  type 'a judgment = { vars : tvar list;
                       indices: Action.indices;
                       theta : Theta.theta;
                       gamma : Gamma.gamma;
                       goal : 'a }

  let pp_judgment pp_goal ppf judge =
    let open Fmt in
    let open Utils in
    pf ppf "@[<v 0>%a@;\
            @[<v 0>%a@]\
            @[<v 0>%a@]\
            @[<hv 2>Theta:@ @[%a@]@]@;\
            Gamma:@;<1 2>@[%a@]@;\
            %a@;\
            %a@;@;@]"
      (fun ppf i -> (styled `Bold ident) ppf (String.make i '=')) 40
      (list ~sep:nop (fun ppf v ->
           pf ppf "%a : %a@;"
             Term.pp_tvar v
             (styled `Blue (styled `Bold ident)) "timestamp"))
      judge.vars
      (list ~sep:nop (fun ppf v ->
           pf ppf "%a : %a@;"
             Action.pp_index v
             (styled `Blue (styled `Bold ident)) "index"))
      judge.indices
      Theta.pp_theta judge.theta
      Gamma.pp_gamma judge.gamma
      (fun ppf i -> (styled `Bold ident) ppf (String.make i '-')) 40
      pp_goal judge.goal

  let init (goal : formula) =
    { vars = [];
      indices = [];
      theta = Theta.mk Term.True;
      gamma = Gamma.mk ();
      goal = goal }

  let rec add_vars vars j = match vars with
    | [] -> j
    | v :: vars ->
      let j' =
        if List.mem v j.vars then j
        else { j with vars = v :: j.vars } in
      add_vars vars j'

  let rec add_indices indices j = match indices with
    | [] -> j
    | i :: indices ->
      let j' =
        if List.mem i j.indices then j
        else { j with indices = i :: j.indices } in
      add_indices indices j'

  let fact_actions f =
    Term.fact_ts f
    |> List.fold_left (fun acc ts -> match action_of_ts ts with
        | None -> acc
        | Some a -> a :: acc
      ) []

  let constr_actions c =
    Term.constr_ts c
    |> List.fold_left (fun acc ts -> match action_of_ts ts with
        | None -> acc
        | Some a -> a :: acc
      ) []

  let update_descr j actions =
    let descrs = List.map Process.get_descr actions in
    let g = List.fold_left Gamma.add_descr j.gamma descrs in
    { j with gamma = g }

  let add_fact f j =
    let j = update_descr j (fact_actions f) in

    { j with gamma = Gamma.add_fact j.gamma f }

  let add_constr c j =
    let j = update_descr j (constr_actions c) in

    { j with theta = Theta.add_constr j.theta c }

  let set_goal_fact f j =
    let j = update_descr j (fact_actions f) in
    { j with goal = f }

  let set_goal a j = { j with goal = a }

  let set_gamma g j = { j with gamma = g }
end

open Judgment


(***********************)
(* Basic Tactics Types *)
(***********************)

type 'a fk = unit -> 'a

type ('a,'b) sk = 'a -> 'b fk -> 'b

type ('a,'b,'c) t = 'a -> ('b,'c) sk -> 'c fk -> 'c


type ('a,'b) mem_fk = 'a -> 'b

type ('a,'b,'c) mem_sk = 'a -> ('b,'c) mem_fk -> 'c

type ('a,'b,'c,'d) mem_t = 'a -> ('b,'c,'d) mem_sk -> ('c,'d) mem_fk -> 'd

(*****************)
(* Basic Tactics *)
(*****************)

let tact_wrap f v sk fk = sk (f v) fk

let tact_return a v = a v (fun r fk' -> r) (fun _ -> raise @@ Failure "return")

let tact_andthen a b sk fk v = a v (fun v fk' -> b v sk fk') fk

let tact_orelse a b sk fk v = a v sk (fun () -> b v sk fk)


(**********************)
(* Introduction Rules *)
(**********************)

let goal_or_intro_l (judge : fact judgment) sk fk = match judge.goal with
  | Or (lgoal, _) -> sk (set_goal_fact lgoal judge) fk
  | _ -> raise @@ Failure "goal ill-formed"

let goal_or_intro_r (judge : fact judgment) sk fk = match judge.goal with
  | Or (_, rgoal) -> sk (set_goal_fact rgoal judge) fk
  | _ -> raise @@ Failure "goal ill-formed"

(** To prove phi \/ psi, try first to prove phi and then psi *)
let goal_or_intro (judge : fact judgment) sk fk =
  tact_orelse goal_or_intro_l goal_or_intro_r sk fk judge

let goal_true_intro (judge : fact judgment) sk fk = match judge.goal with
  | True -> sk () fk
  | _ -> raise @@ Failure "goal ill-formed"

let goal_and_intro (judge : fact judgment) sk fk = match judge.goal with
  | And (lgoal,rgoal) ->
    sk (set_goal_fact lgoal judge) fk;
    sk (set_goal_fact rgoal judge) fk;

  | _ -> raise @@ Failure "goal ill-formed"


(** Introduce the universally quantified variables and the goal. *)
let goal_forall_intro (judge : formula judgment) sk fk =
  let compute_alpha ffresh l l' =
    List.fold_left (fun subst x ->
        if List.mem x l' then (x, ffresh ()) :: subst else (x,x) :: subst
      ) [] l in

  let tsubst = compute_alpha fresh_tvar judge.goal.uvars judge.vars
  and isubst = compute_alpha fresh_index judge.goal.uindices judge.indices in

  let new_cnstr = subst_constr isubst tsubst judge.goal.uconstr
  and new_fact = subst_fact isubst tsubst judge.goal.ufact
  and new_goals =
    List.map (fun goal ->
        subst_postcond isubst tsubst goal
      ) judge.goal.postcond in

  let judge =
    Judgment.set_goal new_goals judge
    |> Judgment.add_indices @@ List.map snd isubst
    |> Judgment.add_vars @@ List.map snd tsubst
    |> Judgment.add_fact new_fact
    |> Judgment.add_constr new_cnstr in

  sk judge fk


(* (\** [goal_exists_intro judge sk fk vnu inu] introduces the existentially
 *     quantified variables and the goal, assuming the constraint on the
 *     existential variables is satisfied (if [force] is true, then the
 *     introduction is done even is the constraint is not satisfied by updating
 *     the judgment constraint.
 *     [vnu] (resp. [inu]) is a mapping from the postcondition existentially binded
 *     timestamp (resp. index) variables to [judge.gamma] timestamp (resp. index)
 *     variables. *\)
 * let goal_exists_intro (judge : postcond judgment) sk fk vnu inu =
 *   let pc_constr = subst_constr inu vnu judge.goal.econstr in
 *
 *   (\* We check whether [judge.theta.constr] implies [pc_constr].
 *      Equivalently, we could check whether:
 *      (Impl (judge.theta.constr,pc_constr)) is satisifable
 *      But [pc_constr] should be usually smaller than [judge.theta], and
 *      therefore it is better to negate [pc_constr], as this yields smaller
 *      formula when we put the constraint in DNF. *\)
 *   let theta' = Theta.add_constr judge.theta (Not pc_constr) in
 *   if not @@ Theta.is_sat theta' then
 *     sk (set_goal judge (subst_postcond inu vnu judge.goal)) fk
 *   else if f then
 *     sk (set_goal judge (subst_postcond inu vnu judge.goal))
 *                     theta = theta' }
 *       fk
 *   else fk () *)


(** [goal_exists_intro judge sk fk vnu inu] introduces the existentially
    quantified variables and the goal.
    [vnu] (resp. [inu]) is a mapping from the postcondition existentially binded
    timestamp (resp. index) variables to [judge.gamma] timestamp (resp. index)
    variables. *)
let goal_exists_intro (judge : postcond judgment) sk fk vnu inu =
  let pc_constr = subst_constr inu vnu judge.goal.econstr in
  let judge = set_goal (subst_fact inu vnu judge.goal.efact) judge
              |> Judgment.add_constr (Not pc_constr) in
  sk judge fk

let goal_intro (judge : fact judgment) sk fk =
  let judge = Judgment.add_fact (Not judge.goal) judge
              |> set_goal_fact False in
  sk judge fk

let fail_goal_false (judge : fact judgment) sk fk = match judge.goal with
  | False -> fk ()
  | _ -> raise @@ Failure "goal ill-formed"

let constr_absurd (judge : 'a judgment) sk fk =
  if not @@ Theta.is_sat judge.theta then sk () fk else fk ()

let gamma_absurd (judge : 'a judgment) sk fk =
  if not @@ Gamma.is_sat judge.gamma then sk () fk else fk ()


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
        Judgment.set_gamma (Gamma.set_facts judge.gamma (fs @ nsel)) judge ) in

  sk judges fk

(** Careful, we do not add action descriptions in new goals here. *)
let rec prove_all (judges : 'a list judgment) tac sk fk =
  match judges.goal with
  | [] -> sk () fk
  | j :: goals ->
    tac (set_goal j judges)
      (fun () fk ->
         prove_all (set_goal goals judges) tac sk fk
      ) fk

(*********)
(* Utils *)
(*********)

let mk_or_cnstr l = match l with
  | [] -> False
  | [a] -> a
  | a :: l' ->
    let rec mk_c acc = function
      | [] -> acc
      | x :: l -> mk_c (Or (x,acc)) l in

    mk_c a l'

let mk_and_cnstr l = match l with
  | [] -> True
  | [a] -> a
  | a :: l' ->
    let rec mk_c acc = function
      | [] -> acc
      | x :: l -> mk_c (And (x,acc)) l in

    mk_c a l'


(*******************)
(* Eq-Indep Axioms *)
(*******************)

(* We include here rules that are specialization of the Eq-Indep axiom. *)

(** Add index constraints resulting from names equalities, modulo the TRS.
    [judge.gamma] must have been completed before calling [eq_names]. *)
let eq_names (judge : 'a judgment) sk fk =
  let atoms = Gamma.get_atoms judge.gamma
  and facts = Gamma.get_facts judge.gamma in

  let all_atoms = List.fold_left (fun l f -> Term.atoms f @ l) atoms facts in
  let terms = List.fold_left (fun acc (_,a,b) -> a :: b :: acc) [] all_atoms in

  let cnstrs = Completion.name_index_cnstrs (Gamma.get_trs judge.gamma) terms in

  let judge =
    List.fold_left (fun judge c ->
        Judgment.add_constr c judge
      ) judge cnstrs in

  sk judge fk


let eq_constants fn (judge : 'a judgment) sk fk =
  let atoms = Gamma.get_atoms judge.gamma
  and facts = Gamma.get_facts judge.gamma in

  let all_atoms = List.fold_left (fun l f -> Term.atoms f @ l) atoms facts in
  let terms = List.fold_left (fun acc (_,a,b) -> a :: b :: acc) [] all_atoms in

  let cnstrs =
    Completion.constant_index_cnstrs fn (Gamma.get_trs judge.gamma) terms in

  let judge =
    List.fold_left (fun judge c ->
        Judgment.add_constr c judge
      ) judge cnstrs in

  sk judge fk

(**************)
(* EUF Axioms *)
(**************)

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


let euf_apply_schema theta (_, (_, key_is), m, s) case =
  let open Euf in
  let open Process in
  (* We create the term equality *)
  let eq = Atom (Eq, case.message, m) in
  let new_f = And (eq, case.blk_descr.condition) in

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


let euf_apply_direct theta (_, (_, key_is), m, _) dcase =
  let open Euf in
  let open Process in

  (* We create the term equality *)
  let eq = Atom (Eq, dcase.d_message, m) in

  (* Now, we need to add the timestamp constraint between [key_is] and
     [dcase.d_key_indices]. *)
  let eq_cnstr =
    List.map2 (fun i i' ->
        Atom (Pind (Eq, i, i'))
      ) key_is dcase.d_key_indices
    |> mk_and_cnstr in

  (eq, eq_cnstr)


let euf_apply_facts judge at = match modulo_sym euf_param at with
  | None -> raise @@ Failure "bad euf application"
  | Some p ->
    let (hash_fn, (key_n, key_is), m, s) = p in
    let rule = Euf.mk_rule m s hash_fn key_n in
    let schemata_premises =
      List.map (fun case ->
          let new_f, new_cnstr = euf_apply_schema judge.theta p case in
          (* let g = Gamma.add_fact judge.gamma new_f in
           * let g = Gamma.add_descr g case.Euf.blk_descr in
           * { judge with theta = Theta.add_constr judge.theta new_cnstr;
           *              gamma = g } *)
          Judgment.add_fact new_f judge
          |> Judgment.add_constr new_cnstr
          |> Judgment.add_indices case.Euf.blk_descr.Process.indices
        ) rule.Euf.case_schemata

    and direct_premises =
      List.map (fun case ->
          let new_f, new_cnstr = euf_apply_direct judge.theta p case in
          Judgment.add_fact new_f judge
          |> Judgment.add_constr new_cnstr
        ) rule.Euf.cases_direct in

    schemata_premises @ direct_premises

let euf_apply (judge : 'a judgment) sk fk f_select =
  let g, at = Gamma.select judge.gamma f_select (set_euf true) in
  let judge = Judgment.set_gamma g judge in

  (* TODO: need to handle failure somewhere. *)
  sk (euf_apply_facts judge at) fk


(***********)
(* Tactics *)
(***********)

(** Tactics expression *)
type (_,_) tac =
  | Admit : ('a judgment, unit) tac

  | GoalOrIntroL : (fact judgment, fact judgment) tac
  | GoalOrIntroR : (fact judgment, fact judgment) tac
  | GoalIntro : (fact judgment, fact judgment) tac
  | GoalAndIntro : (fact judgment, fact judgment) tac

  | GoalForallIntro : (formula judgment, postcond list judgment) tac
  | GoalExistsIntro :
      tvar subst * index subst ->
    (postcond judgment, fact judgment) tac

  | GammaAbsurd : ('a judgment, unit) tac
  | ConstrAbsurd : ('a judgment, unit) tac

  | EqNames : ('a judgment, 'a judgment) tac
  | EqConstants : fname -> ('a judgment, 'a judgment) tac

  | ProveAll : ('a judgment, unit) tac -> ('a list judgment, unit) tac
  | AndThen : ('a,'b) tac * ('b,'c) tac -> ('a,'c) tac
  | OrElse : ('a,'b) tac * ('a,'b) tac -> ('a,'b) tac

let rec tac_apply :
  type a b c. (a,b) tac -> a -> (b,c) sk -> c fk -> c =
  fun tac judge sk fk -> match tac with
    | Admit -> sk () fk

    | GoalForallIntro -> goal_forall_intro judge sk fk
    | GoalExistsIntro (vnu,inu) -> goal_exists_intro judge sk fk vnu inu

    | GoalOrIntroL -> goal_or_intro_l judge sk fk
    | GoalOrIntroR -> goal_or_intro_r judge sk fk
    | GoalAndIntro -> goal_and_intro judge sk fk
    | GoalIntro -> goal_intro judge sk fk

    | GammaAbsurd -> gamma_absurd judge sk fk
    | ConstrAbsurd -> constr_absurd judge sk fk

    | EqNames -> eq_names judge sk fk
    | EqConstants fn -> eq_constants fn judge sk fk

    | ProveAll tac -> prove_all judge (tac_apply tac) sk fk
    | AndThen (tac,tac') ->
      tact_andthen (tac_apply tac) (tac_apply tac') sk fk judge
    | OrElse (tac,tac') ->
      tact_orelse (tac_apply tac) (tac_apply tac') sk fk judge


type gtvar = Gtvar

type _ goaltype =
  | Gt_var : gtvar goaltype

  | Gt_unit : unit goaltype
  | Gt_formula : formula goaltype
  | Gt_postcond : postcond goaltype
  | Gt_fact : fact goaltype
  | Gt_judgment : 'a goaltype -> 'a judgment goaltype
  | Gt_list : 'a goaltype -> 'a list goaltype

type 'a gt = 'a goaltype

type utac =
  | UAdmit
  | UGoalOrIntroL of utac
  | UGammaAbsurd
  | UAndThen of utac * utac
  | UOrElse of utac * utac

type etac = | ETac : 'a goaltype * 'b goaltype * ('a,'b) tac -> etac

exception Tactic_type_error

let rec check_eq : type a b. a gt -> b gt -> a -> b =
  fun agt bgt a -> match agt,bgt with
  | Gt_fact, Gt_fact -> a
  | Gt_formula, Gt_formula -> a
  | Gt_postcond, Gt_postcond -> a
  | Gt_list l, Gt_list l' -> List.map (check_eq l l') a

  | _ -> raise Tactic_type_error

(* let rec subtype : type a b. a gt -> b gt -> a gt =
 *   fun a b -> match a,b with
 *     | _, Gt_var -> a
 *     | Gt_fact, Gt_fact -> a
 *     | Gt_formula, Gt_formula -> a
 *     | Gt_postcond, Gt_postcond -> a
 *     | Gt_list l, Gt_list l' -> Gt_list (subtype l l')
 *
 *     | _ -> raise Tactic_type_error *)

let check_unit : type a. a gt -> unit gt = function
  | Gt_unit -> Gt_unit
  | Gt_var -> Gt_unit
  | _ -> raise Tactic_type_error

let check_type : type a b. a gt -> b gt -> utac -> (a,b) tac =
  fun _ _ _ -> assert false

let rec tac_type : type a b. a gt -> b gt -> utac -> etac =
  fun l_gt r_gt utac -> match utac with
    | UAdmit -> begin match l_gt with
        | Gt_var -> ETac ( Gt_judgment Gt_var,
                           check_unit r_gt,
                           Admit )
        | Gt_judgment _ -> ETac ( l_gt,
                                  check_unit r_gt,
                                  Admit )
        | _ -> raise Tactic_type_error end

    | UOrElse (utac_l, utac_r) -> begin match tac_type l_gt r_gt utac_l with
        | ETac (l_gt, r_gt, _) -> match tac_type l_gt r_gt utac_r with
          | ETac (l_gt, r_gt, tac_r) ->
            let tac_l = check_type l_gt r_gt utac_l in
            ETac (l_gt, r_gt, OrElse (tac_l, tac_r)) end

    | _ -> assert false


(* let () =
 *   Checks.add_suite "Logic" [
 *     "Empty", `Quick,
 *     begin fun () -> ()
 *     end
 *   ] *)
