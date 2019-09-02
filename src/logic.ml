open Utils
open Action
open Term


let rec action_of_ts = function
  | TName a -> Some a
  | TPred ts -> action_of_ts ts
  | TVar _ -> None

(** Tags used to record some information on gamma elements:
    - [euf] records whether the EUF axiom has been applied. *)
type tag = { t_euf : bool; cpt : int }

let cpt_tag = ref 0

let new_tag () =
  let t = { t_euf = false; cpt = !cpt_tag } in
  incr cpt_tag;
  t

let set_euf b t = { t with t_euf = b }


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

  val get_all_terms :gamma -> Term.term list
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
                @[<hv 0>Atoms:@ @[<v 0>%a@]@]@;\
                @[<hv 0>Facts:@ @[<v 0>%a@]@]@;@]"
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") Action.pp_action)
      gamma.actions_described
      (Fmt.list (fun ppf (at,t) ->
           Fmt.pf ppf "%d: %a" t.cpt Term.pp_atom at)) (List.rev gamma.atoms)
      (Fmt.list Term.pp_fact) (List.rev gamma.facts)

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

  (* Provides the list of all terms appearing inside atoms or facts of the Gamma *)
  let get_all_terms g =
    let atoms = get_atoms g
    and facts = get_facts g in

    let all_atoms = List.fold_left (fun l f -> Term.atoms f @ l) atoms facts in
    List.fold_left (fun acc (_,a,b) -> a :: b :: acc) [] all_atoms

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

  val get_equalities : theta -> timestamp list list
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

  let get_equalities theta =
    compute_models theta;
    let ts = Term.constr_ts theta.constr |> List.sort_uniq Pervasives.compare in
    Constr.get_equalities (opt_get !(theta.models)) ts
  
end

(** Type of goal types *)

type gtlat

(** Type of goal types.
    [Gt_top] and [Gt_bot] are, respectively, the top and bottom element of the
    type lattice, and are for the type checking. *)
type _ goaltype =
  | Gt_top : gtlat goaltype
  | Gt_bot : gtlat goaltype

  | Gt_unit : unit goaltype
  | Gt_formula : formula goaltype
  | Gt_postcond : postcond goaltype
  | Gt_fact : fact goaltype

type 'a gt = 'a goaltype

let rec pp_gt : type a. Format.formatter -> a gt -> unit = fun ppf gt ->
  match gt with
  | Gt_bot -> Fmt.pf ppf "bot"
  | Gt_top -> Fmt.pf ppf "top"
  | Gt_unit -> Fmt.pf ppf "unit"
  | Gt_formula -> Fmt.pf ppf "formula"
  | Gt_postcond -> Fmt.pf ppf "postcond"
  | Gt_fact -> Fmt.pf ppf "fact"

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
                               goal : 'a;
                               gt : 'a gt }

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

  val set_goal : 'b -> 'b gt -> 'a judgment -> 'b judgment

  val set_gamma : Gamma.gamma -> 'a judgment ->  'a judgment
end = struct
  type 'a judgment = { vars : tvar list;
                       indices: Action.indices;
                       theta : Theta.theta;
                       gamma : Gamma.gamma;
                       goal : 'a;
                       gt : 'a gt }

  let pp_judgment pp_goal ppf judge =
    let open Fmt in
    let open Utils in
    pf ppf "@[<v 0>%a@;\
            @[<v 0>%a@]\
            @[<v 0>%a@]\
            @[<hv 2>Theta:@ @[%a@]@]@;\
            @[%a@]@;\
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
      goal = goal;
      gt = Gt_formula }

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
    { j with goal = f; gt = Gt_fact }

  let set_goal a agt j = { j with goal = a; gt = agt }

  let set_gamma g j = { j with gamma = g }
end

open Judgment


(** Basic Tactics Types *)

type 'a fk = unit -> 'a

type ('a,'b) sk = 'a -> 'b fk -> 'b

type ('a,'b,'c) t = 'a -> ('b,'c) sk -> 'c fk -> 'c


type ('a,'b) mem_fk = 'a -> 'b

type ('a,'b,'c) mem_sk = 'a -> ('b,'c) mem_fk -> 'c

type ('a,'b,'c,'d) mem_t = 'a -> ('b,'c,'d) mem_sk -> ('c,'d) mem_fk -> 'd


(** Basic Tactics *)

let tact_wrap f v sk fk = sk (f v) fk

let tact_return a v = a v (fun r fk' -> r) (fun _ -> raise @@ Failure "return")

let tact_andthen a b sk fk v = a v (fun v fk' -> b v sk fk') fk

let tact_orelse a b sk fk v = a v sk (fun () -> b v sk fk)

let lift : ('a,'b list,'b list) t -> ('a list,'b list,'b list) t =
  fun tac vs sk fk ->
    let exception Suc_fail in
    let comp_vs' () =
      List.fold_left (fun acc v ->
          tac v (fun l _ -> l) (fun () -> raise Suc_fail)
          @ acc
        ) [] vs in

    (* We catch the exception before calling the continuation. *)
    let opt_vs' = try Some (comp_vs' ()) with Suc_fail -> None in
    match opt_vs' with
    | Some vs' -> sk vs' fk
    | None -> fk ()

(** Introduction Rules *)

let goal_or_intro_l (judge : fact judgment) sk fk = match judge.goal with
  | Or (lgoal, _) -> sk [set_goal_fact lgoal judge] fk
  | _ -> raise @@ Failure "goal ill-formed"

let goal_or_intro_r (judge : fact judgment) sk fk = match judge.goal with
  | Or (_, rgoal) -> sk [set_goal_fact rgoal judge] fk
  | _ -> raise @@ Failure "goal ill-formed"

(** To prove phi \/ psi, try first to prove phi and then psi *)
let goal_or_intro (judge : fact judgment) sk fk =
  tact_orelse goal_or_intro_l goal_or_intro_r sk fk judge

let goal_true_intro (judge : fact judgment) sk fk = match judge.goal with
  | True -> sk () fk
  | _ -> raise @@ Failure "goal ill-formed"

let goal_and_intro (judge : fact judgment) sk fk = match judge.goal with
  | And (lgoal,rgoal) ->
    sk [ set_goal_fact lgoal judge;
         set_goal_fact rgoal judge ] fk;

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

  let judges =
    List.map (fun goal ->
        Judgment.set_goal goal Gt_postcond judge
        |> Judgment.add_indices @@ List.map snd isubst
        |> Judgment.add_vars @@ List.map snd tsubst
        |> Judgment.add_fact new_fact
        |> Judgment.add_constr new_cnstr
      ) new_goals in

  sk judges fk



(** [goal_exists_intro judge sk fk vnu inu] introduces the existentially
    quantified variables and the goal.
    [vnu] (resp. [inu]) is a mapping from the postcondition existentially binded
    timestamp (resp. index) variables to [judge.gamma] timestamp (resp. index)
    variables. *)
let goal_exists_intro (judge : postcond judgment) sk fk vnu inu =
  let pc_constr = subst_constr inu vnu judge.goal.econstr in
  let judge = set_goal (subst_fact inu vnu judge.goal.efact) Gt_fact judge
              |> Judgment.add_constr (Not pc_constr) in
  sk [judge] fk

let goal_intro (judge : fact judgment) sk fk =
  let judge = Judgment.add_fact (Not judge.goal) judge
              |> set_goal_fact False in
  sk [judge] fk

let fail_goal_false (judge : fact judgment) sk fk = match judge.goal with
  | False -> fk ()
  | _ -> raise @@ Failure "goal ill-formed"

let constr_absurd (judge : 'a judgment) sk fk =
  if not @@ Theta.is_sat judge.theta then
    sk [Judgment.set_goal () Gt_unit judge] fk
  else fk ()

let gamma_absurd (judge : 'a judgment) sk fk =
  if not @@ Gamma.is_sat judge.gamma then
    sk [Judgment.set_goal () Gt_unit judge] fk
  else fk ()


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

(* (\** Careful, we do not add action descriptions in new goals here.
 *     Give to the continuation [sk] the last judgment in the list, if it exists. *\)
 * let rec prove_all ?last:(last=None) (judges : 'a list judgment) tac sk fk =
 *   match judges.goal with
 *   | [] -> begin match last with
 *       | None -> sk (Judgment.set_goal () Gt_unit judges) fk
 *       | Some judge -> sk judge fk end
 *   | j :: goals ->
 *     let jgt = match judges.gt with Gt_list jt -> jt in
 *     tac (set_goal j jgt judges)
 *       (fun last fk ->
 *          prove_all ~last:(Some last) (set_goal goals judges.gt judges) tac sk fk
 *       ) fk *)



(** Utils *)

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


(** Eq-Indep Axioms *)

(* We include here rules that are specialization of the Eq-Indep axiom. *)

(** Add index constraints resulting from names equalities, modulo the TRS.
    [judge.gamma] must have been completed before calling [eq_names]. *)
let eq_names (judge : 'a judgment) sk fk =
  let cnstrs = Completion.name_index_cnstrs (Gamma.get_trs judge.gamma)
      (Gamma.get_all_terms judge.gamma) in

  let judge =
    List.fold_left (fun judge c ->
        Judgment.add_constr c judge
      ) judge cnstrs in

  sk [judge] fk

let eq_constants fn (judge : 'a judgment) sk fk =
  let cnstrs =
    Completion.constant_index_cnstrs fn (Gamma.get_trs judge.gamma)
      (Gamma.get_all_terms judge.gamma) in
  let judge =
    List.fold_left (fun judge c ->
        Judgment.add_constr c judge
      ) judge cnstrs in

  sk [judge] fk

let eq_timestamps (judge : 'a judgment) sk fk =
  let ts_classes = Theta.get_equalities judge.theta
           |> List.map (List.sort_uniq Pervasives.compare)
  in
  List.iter (fun x -> Format.printf "[";  List.iter (fun t -> Format.printf "%a," pp_timestamp t)  x;Format.printf "]"    ) ts_classes;
  let norm ts =
    try
      List.find (List.mem ts) ts_classes |> List.hd
    with Not_found -> ts
  in
  
  let terms = (Gamma.get_all_terms judge.gamma) in
  let facts = List.fold_left (fun acc t ->
      let normt =  Constr.ts_normalize norm t in
      Format.printf "t: %a, nt :%a" Term.pp_term t Term.pp_term normt; 
      if normt = t then
        acc
      else
        Atom( (Eq, t,normt))::acc ) [] terms in
  let judge =
    List.fold_left (fun judge c ->
        Judgment.add_fact c judge
      ) judge facts in

  sk [judge] fk


(** EUF Axioms *)

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

let euf_apply f_select (judge : 'a judgment) sk fk =
  let g, at = Gamma.select judge.gamma f_select (set_euf true) in
  let judge = Judgment.set_gamma g judge in

  (* TODO: need to handle failure somewhere. *)
  sk (euf_apply_facts judge at) fk


(** Tactics *)

(** Tactics expression *)
type (_,_) tac =
  | Admit : ('a, unit) tac
  | Ident : ('a,'a) tac

  | Left : (fact, fact) tac
  | Right : (fact, fact) tac
  | Intro : (fact, fact) tac
  | Split : (fact, fact) tac

  | ForallIntro : (formula, postcond) tac
  | ExistsIntro :
      tvar subst * index subst ->
    (postcond, fact) tac

  | GammaAbsurd : ('a, unit) tac
  | ConstrAbsurd : ('a, unit) tac

  | EqNames : ('a, 'a) tac
  | EqTimestamps : ('a, 'a) tac
  | EqConstants : fname -> ('a, 'a) tac

  (* | ProveAll : ('a, unit) tac -> ('a list, unit) tac *)
  | AndThen : ('a,'b) tac * ('b,'c) tac * 'b gt -> ('a,'c) tac
  | OrElse : ('a,'b) tac * ('a,'b) tac -> ('a,'b) tac
  | Try : ('a, unit) tac * ('a,'a) tac -> ('a,'a) tac

  | Euf : int -> ('a, 'a) tac

  | Cycle : int -> ('a, 'a) tac

  (* | TacPrint : ('a,'b) tac -> ('a,'b) tac *)


let rec pp_tac : type a b. Format.formatter -> (a,b) tac -> unit =
  fun ppf tac -> match tac with
    | Admit -> Fmt.pf ppf "admit"
    | Ident -> Fmt.pf ppf "ident"

    | Left -> Fmt.pf ppf "goal_or_intro_l"
    | Right -> Fmt.pf ppf "goal_or_intro_r"
    | Intro -> Fmt.pf ppf "goal_intro"
    | Split -> Fmt.pf ppf "goal_and_intro"

    | ForallIntro -> Fmt.pf ppf "forall_intro"
    | ExistsIntro (vnu,inu) ->
      Fmt.pf ppf "@[<v 2>exists_intro@;%a@;%a@]"
        (pp_subst pp_tvar) vnu
        (pp_subst pp_index) inu

    | GammaAbsurd -> Fmt.pf ppf "gamma_absurd"
    | ConstrAbsurd -> Fmt.pf ppf "constr_absurd"

    | EqNames -> Fmt.pf ppf "eq_names"
    | EqTimestamps -> Fmt.pf ppf "eq_timestamps"                   
    | EqConstants fn -> Fmt.pf ppf "eq_constants %a" pp_fname fn

    (* | ProveAll utac -> Fmt.pf ppf "apply_all(@[%a@])" pp_tac utac *)
    | AndThen (ut, ut',_) ->
      Fmt.pf ppf "@[%a@]; @,@[%a@]" pp_tac ut pp_tac ut'
    | OrElse (ut, ut') ->
      Fmt.pf ppf "@[%a@] + @,@[%a@]" pp_tac ut pp_tac ut'
    | Try (ut, ut') ->
      Fmt.pf ppf "try@[%a@] orelse @,@[%a@]" pp_tac ut pp_tac ut'

    (* | TacPrint ut -> Fmt.pf ppf "@[%a@].@;" pp_tac ut *)

    | Euf i -> Fmt.pf ppf "euf %d" i
    | Cycle i -> Fmt.pf ppf "cycle %d" i

let rec pp_gt_el : type a. a gt -> Format.formatter -> a -> unit =
  fun gt ppf a -> match gt with
    | Gt_top -> assert false
    | Gt_bot -> assert false    (* Gtvar is not inhabited. *)
    | Gt_unit -> Fmt.pf ppf "()"
    | Gt_fact -> pp_fact ppf a
    | Gt_postcond -> pp_postcond ppf a
    | Gt_formula -> pp_formula ppf a


let rec tac_apply :
  type a b c.
  b gt -> (a,b) tac -> a judgment ->
  (b judgment list, c) sk ->
  c fk -> c =
  fun gt tac judge sk fk -> match tac with
    | Admit -> sk [Judgment.set_goal () Gt_unit judge] fk
    | Ident -> sk [judge] fk

    | ForallIntro -> goal_forall_intro judge sk fk
    | ExistsIntro (vnu,inu) -> goal_exists_intro judge sk fk vnu inu

    | Left -> goal_or_intro_l judge sk fk
    | Right -> goal_or_intro_r judge sk fk
    | Split -> goal_and_intro judge sk fk
    | Intro -> goal_intro judge sk fk

    | GammaAbsurd -> gamma_absurd judge sk fk
    | ConstrAbsurd -> constr_absurd judge sk fk

    | EqNames -> eq_names judge sk fk
    | EqTimestamps -> eq_timestamps judge sk fk                   
    | EqConstants fn -> eq_constants fn judge sk fk
    | Euf i ->
      let f_select _ t = t.cpt = i in
      euf_apply f_select judge sk fk

    (* | ProveAll tac -> prove_all judge (tac_apply gt tac) sk fk *)

    | AndThen (tac,tac',mid_gt) ->
      let suc_k judges sk fk =
        let exception Suc_fail in
        let compute_judges () =
          List.fold_left (fun acc judge ->
              let new_j =
                tac_apply gt tac' judge
                  (fun l _ -> l)
                  (fun () -> raise Suc_fail) in
              new_j @ acc
            ) [] judges in

        (* We catch the exception before calling the continuation. *)
        match compute_judges () with
        | judges -> sk judges fk
        | exception Suc_fail -> fk () in

      tact_andthen
        (tac_apply mid_gt tac)
        suc_k
        sk fk judge

    | OrElse (tac,tac') ->
      tact_orelse (tac_apply gt tac) (tac_apply gt tac') sk fk judge

    | Try (tac,tac') ->
      tac_apply Gt_unit tac judge (fun _ fk -> sk [] fk)
        (fun () -> tac_apply gt tac' judge sk fk)

    | Cycle _ -> assert false   (* This is not a focused tactic. *)

    (* | TacPrint tac ->
     *   Fmt.pr "%a @[<hov 0>%a@]@;%!"
     *     (Fmt.styled `Bold ident) "Tactic:" pp_tac tac;
     *   tac_apply gt tac judge (fun judge fk ->
     *       Fmt.pr "%a%!" (Judgment.pp_judgment (pp_gt_el gt)) judge;
     *       sk judge fk)
     *     fk *)


(** Tactic Parsing and Type-Checking *)

let rec pp_tact_type : type a b. Format.formatter -> (a gt * b gt) -> unit =
  fun ppf (gt,gt') ->
    Fmt.pf ppf "@[<hv 0>%a@ %a@ %a@]"
      pp_gt gt
      Fmt.(styled `Red (styled `Underline ident)) "=>"
      pp_gt gt'

(** Flip [Gt_bot] element to [Gt_top]. *)
let rec bot_to_top : type a. a gt -> a gt = function
  | Gt_bot -> Gt_top
  | Gt_top -> assert false
  | Gt_unit -> Gt_unit
  | Gt_formula -> Gt_formula
  | Gt_postcond -> Gt_postcond
  | Gt_fact -> Gt_fact
  (* | Gt_list lt -> Gt_list (bot_to_top lt) *)

(** Flip [Gt_top] element to [Gt_bot]. *)
let rec top_to_bot : type a. a gt -> a gt = function
  | Gt_top -> Gt_bot
  | Gt_bot -> assert false
  | Gt_unit -> Gt_unit
  | Gt_formula -> Gt_formula
  | Gt_postcond -> Gt_postcond
  | Gt_fact -> Gt_fact
  (* | Gt_list lt -> Gt_list (top_to_bot lt) *)

(** Type for untyped tacitcs.
    [UAndThen] can optionally be decorated with the tactic intermediate type,
    which uses only [Gt_top]. *)
type utac =
  | UAdmit : utac
  | UIdent : utac

  | ULeft : utac
  | URight : utac
  | UIntro : utac
  | USplit : utac

  | UForallIntro : utac
  | UExistsIntro : tvar subst * index subst -> utac

  | UGammaAbsurd : utac
  | UConstrAbsurd : utac

  | UEqNames : utac
  | UEqTimestamps : utac      
  | UEqConstants : fname -> utac

  (* | UProveAll : utac -> utac *)
  | UAndThen : utac * utac * 'a gt option -> utac
  | UOrElse : utac * utac -> utac
  | UTry : utac * utac -> utac

  | UEuf : int -> utac
  | UCycle : int -> utac

  (* | UPrint : utac -> utac *)

let rec pp_utac ppf = function
  | UAdmit -> Fmt.pf ppf "admit"
  | UIdent -> Fmt.pf ppf "ident"

  | ULeft -> Fmt.pf ppf "goal_or_intro_l"
  | URight -> Fmt.pf ppf "goal_or_intro_r"
  | UIntro -> Fmt.pf ppf "goal_intro"
  | USplit -> Fmt.pf ppf "goal_and_intro"

  | UForallIntro -> Fmt.pf ppf "forall_intro"
  | UExistsIntro (vnu,inu) ->
    Fmt.pf ppf "@[<v 2>exists_intro@;%a@;%a@]"
      (pp_subst pp_tvar) vnu
      (pp_subst pp_index) inu

  | UGammaAbsurd -> Fmt.pf ppf "gamma_absurd"
  | UConstrAbsurd -> Fmt.pf ppf "constr_absurd"

  | UEqNames -> Fmt.pf ppf "eq_names"
  | UEqTimestamps -> Fmt.pf ppf "eq_timestamps"                  
  | UEqConstants fn -> Fmt.pf ppf "eq_constants %a" pp_fname fn

  (* | UProveAll utac -> Fmt.pf ppf "apply_all(@[%a@])" pp_utac utac *)
  | UAndThen (ut, ut',_) ->
    Fmt.pf ppf "@[%a@];@[%a@]" pp_utac ut pp_utac ut'
  | UOrElse (ut, ut') ->
    Fmt.pf ppf "@[%a@]+@[%a@]" pp_utac ut pp_utac ut'
  | UTry (ut, ut') ->
    Fmt.pf ppf "try@[%a@] orelse @,@[%a@]" pp_utac ut pp_utac ut'

  | UEuf i -> Fmt.pf ppf "euf %d" i
  | UCycle i -> Fmt.pf ppf "cycle %d" i

  (* | UPrint ut -> Fmt.pf ppf "@[%a@].@;" pp_utac ut *)

(** Existential type for tactics. *)
type etac = | ETac : 'a gt * 'b gt * ('a,'b) tac -> etac


exception Tactic_type_error

let rec subtype : type a b. a gt -> b gt -> bool =
  fun agt bgt -> match agt,bgt with
    | _, Gt_top -> true
    | Gt_bot, _ -> true
    | Gt_unit, Gt_unit -> true
    | Gt_fact, Gt_fact -> true
    | Gt_formula, Gt_formula -> true
    | Gt_postcond, Gt_postcond -> true
    (* | Gt_list lt, Gt_list lt' -> subtype lt lt' *)
    | _ -> false

let rec check_eq : type a b. a gt -> b gt -> a -> b =
  fun agt bgt a -> match agt,bgt with
    | Gt_bot, _ -> assert false
    | Gt_top, _ -> assert false
    | _, Gt_bot -> assert false
    | _, Gt_top -> assert false (* Gt_lat is not inhabited *)

    | Gt_unit, Gt_unit -> a
    | Gt_fact, Gt_fact -> a
    | Gt_formula, Gt_formula -> a
    | Gt_postcond, Gt_postcond -> a

    (* | Gt_list lt, Gt_list lt' -> List.map (check_eq lt lt') a *)

    | _ ->
      Log.log Log.LogTacticTC (fun () ->
          Fmt.epr "@[%a@] is not a equal to @[%a@]@;%!" pp_gt agt pp_gt bgt);
      raise Tactic_type_error

let check_unit : type a. a gt -> unit gt = function
  | Gt_unit -> Gt_unit
  | Gt_bot -> Gt_unit
  | _ as gt ->
    Log.log Log.LogTacticTC (fun () ->
        Fmt.epr "@[%a@] is not a subtype of @[%a@]@;%!" pp_gt gt pp_gt Gt_unit);
    raise Tactic_type_error

let tac_of_simp_utac utac = match utac with
  | ULeft -> Left
  | URight -> Right
  | UIntro -> Intro
  | USplit -> Split
  | _ -> assert false

let tac_of_simp_utac2 utac = match utac with
  | UIdent -> Ident
  | UEqNames -> EqNames
  | UEqTimestamps -> EqTimestamps
  | UEqConstants fn -> EqConstants fn
  | UEuf i -> Euf i
  | UCycle i -> Cycle i
  | _ -> assert false

let tac_of_simp_utac3 utac = match utac with
  | UAdmit -> Admit
  | UGammaAbsurd -> GammaAbsurd
  | UConstrAbsurd -> ConstrAbsurd
  | _ -> assert false

type (_,_) eq_type = | Refl : 'a * 'a -> ('a, 'a) eq_type

let rec get_refl : type a b. a gt -> b gt -> (a gt, b gt) eq_type option =
  fun a b -> match a, b with
    | Gt_bot, Gt_bot -> Refl (a,b) |> some
    | Gt_top, Gt_top -> Refl (a,b) |> some
    | Gt_unit, Gt_unit -> Refl (a,b) |> some
    | Gt_formula, Gt_formula -> Refl (a,b) |> some
    | Gt_postcond, Gt_postcond -> Refl (a,b) |> some
    | Gt_fact, Gt_fact -> Refl (a,b) |> some
    (* | Gt_list l, Gt_list r -> begin match get_refl l r with
     *     | Some (Refl _) -> Refl (a,b) |> some
     *     | None -> None end *)
    | _ -> None

let fail_check_type : type a b. a gt -> b gt -> utac -> exn =
  fun l_gt r_gt utac ->
    Log.log Log.LogTacticTC (fun () ->
        Fmt.epr "@[<hv 0>%a@ cannot be given the type@ \
                 %a]@;%!"
          pp_utac utac
          pp_tact_type (l_gt,r_gt));
    Tactic_type_error

(** [check_type l_gt r_gt utac] checks that [l_gt] -> [r_gt] is a valid type of
    [utac]. Requires all [UAndThen] tactic to be decorated with the intermediate
    types. *)
let rec check_type : type a b. a gt -> b gt -> utac -> (a,b) tac =
  fun l_gt r_gt utac -> match utac with
    | UAdmit | UGammaAbsurd | UConstrAbsurd -> begin match r_gt with
        | Gt_unit -> tac_of_simp_utac3 utac
        | _ -> raise @@ fail_check_type l_gt r_gt utac end

    | ULeft | URight | UIntro | USplit ->
      begin match l_gt, r_gt with
        | Gt_fact, Gt_fact -> tac_of_simp_utac utac
        | _ -> raise @@ fail_check_type l_gt r_gt utac end

    | UEqNames | UEqTimestamps | UEqConstants _ | UEuf _ | UIdent | UCycle _ ->
      begin match get_refl l_gt r_gt with
        | Some (Refl _) -> tac_of_simp_utac2 utac
        | None -> raise @@ fail_check_type l_gt r_gt utac end

    | UForallIntro -> begin match l_gt, r_gt with
        | Gt_formula, Gt_postcond -> ForallIntro
        | _ -> raise @@ fail_check_type l_gt r_gt utac end

    | UExistsIntro (vnu,inu) -> begin match l_gt, r_gt with
        | Gt_postcond, Gt_fact -> ExistsIntro (vnu,inu)
        | _ -> raise @@ fail_check_type l_gt r_gt utac end

    (* | UProveAll utac' -> begin match l_gt, r_gt with
     *     | Gt_list jt, Gt_unit -> ProveAll (check_type jt Gt_unit utac')
     *     | _ -> raise @@ fail_check_type l_gt r_gt utac end *)

    | UOrElse (utac_l, utac_r) ->
      let tac_l = check_type l_gt r_gt utac_l
      and tac_r = check_type l_gt r_gt utac_r in
      OrElse (tac_l, tac_r)

    | UAndThen (utac_l, utac_r, Some mid_gt) ->
      let tac_l = check_type l_gt (top_to_bot mid_gt) utac_l
      and tac_r = check_type mid_gt r_gt utac_r in
      AndThen (tac_l, tac_r, mid_gt)

    | UTry (utac_l, utac_r) -> begin match get_refl l_gt r_gt with
        | Some (Refl _) ->
          let tac_l = check_type l_gt Gt_unit utac_l
          and tac_r = check_type l_gt r_gt utac_r in
          Try (tac_l, tac_r)

        | None -> raise @@ fail_check_type l_gt r_gt utac end

    (* | UPrint utac' -> TacPrint (check_type l_gt r_gt utac') *)
    | UAndThen (utac_l, utac_r, None) -> assert false


let fail_tac_type : type a b. a gt -> b gt -> utac -> exn =
  fun l_gt r_gt utac ->
    Log.log Log.LogTacticTC (fun () ->
        Fmt.epr "@[<hv 0>%a@ cannot be type in the context@ \
                 %a@]@;%!"
          pp_utac utac
          pp_tact_type (l_gt,r_gt));
    Tactic_type_error

(** [tac_typ l_gt r_gt utac] infers the most general type of an untyped tactic,
    knowing that the left type must be a subtype of [l_gt], and [r_gt] must be
    a subtype of the right type.
    Returns a pair [(utac', etac')], where [etac'] is the typed tactic
    (wrapped), and [utac'] is the original untyped tactic decorated with types
    information at the [UAndThen] node (necessary for the type_checking).  *)
let rec tac_typ : type a b. a gt -> b gt -> utac -> utac * etac =
  fun l_gt r_gt utac -> match utac with
    | UAdmit | UGammaAbsurd | UConstrAbsurd ->
      ( utac, ETac ( l_gt,
                     check_unit r_gt,
                     tac_of_simp_utac3 utac ))

    | ULeft | URight | UIntro | USplit ->
      if subtype Gt_fact l_gt
      && subtype r_gt Gt_fact then
        ( utac, ETac ( Gt_fact, Gt_fact, tac_of_simp_utac utac ))
      else raise @@ fail_tac_type l_gt r_gt utac

    | UIdent | UEqNames | UEqTimestamps | UEqConstants _ | UEuf _ | UCycle _ ->
      begin match l_gt, r_gt with
        | Gt_top, Gt_bot ->
          ( utac, ETac ( Gt_top, Gt_bot, tac_of_simp_utac2 utac ))
        | Gt_top, jt ->
          ( utac, ETac ( r_gt, r_gt, tac_of_simp_utac2 utac ))
        | jt, Gt_bot ->
          ( utac, ETac ( l_gt, l_gt, tac_of_simp_utac2 utac ))
        | jt, jt' ->
          if subtype jt jt' then
            ( utac, ETac ( l_gt, top_to_bot l_gt, tac_of_simp_utac2 utac ))
          else if subtype jt' jt then
            ( utac, ETac ( bot_to_top r_gt, r_gt, tac_of_simp_utac2 utac ))
          else raise @@ fail_tac_type l_gt r_gt utac end

    | UTry (utac_l, utac_r) ->
      begin match tac_typ l_gt Gt_unit utac_l with
        | utac_l', ETac (l_gt, _, _) -> match tac_typ l_gt r_gt utac_r with
          | utac_r', ETac (l_gt, r_gt, tac_r) -> match l_gt, r_gt with
            | Gt_top, Gt_bot ->
              let tac_l = check_type l_gt Gt_unit utac_l' in
              ( UTry (utac_l', utac_r'),
                ETac ( Gt_top, Gt_bot, Try (tac_l, tac_r)) )
            | Gt_top, _ ->
              let tac_l = check_type r_gt Gt_unit utac_l' in
              let tac_r = check_type r_gt r_gt utac_r' in
              ( UTry (utac_l', utac_r'),
                ETac ( r_gt, r_gt, Try (tac_l, tac_r)) )

            | _, Gt_bot ->
              let tac_l = check_type l_gt Gt_unit utac_l' in
              let tac_r = check_type l_gt l_gt utac_r' in
              ( UTry (utac_l', utac_r'),
                ETac ( l_gt, l_gt, Try (tac_l, tac_r)) )

            | _, _ -> match get_refl l_gt r_gt with
              | None -> raise @@ fail_tac_type l_gt r_gt utac
              | Some (Refl _) ->
                let tac_l = check_type r_gt Gt_unit utac_l' in
                ( UTry (utac_l', utac_r'),
                  ETac ( l_gt, r_gt, Try (tac_l, tac_r)) ) end

    | UForallIntro ->
      if subtype Gt_formula l_gt
      && subtype r_gt Gt_postcond then
        ( utac, ETac ( Gt_formula,
                       Gt_postcond,
                       ForallIntro ))
      else raise @@ fail_tac_type l_gt r_gt utac

    | UExistsIntro (vnu,inu) ->
      if subtype Gt_postcond l_gt
      && subtype r_gt Gt_fact then
        ( utac, ETac ( Gt_postcond,
                       Gt_fact,
                       ExistsIntro (vnu,inu) ))
      else raise @@ fail_tac_type l_gt r_gt utac

    (* | UProveAll utac' ->
     *   let type_prove_all : type a. a gt -> utac * etac = fun in_l_gt ->
     *     match tac_typ in_l_gt (check_unit r_gt) utac' with
     *     | utac', ETac (jt, r_gt, tac) ->
     *       match get_refl r_gt Gt_unit with
     *       | Some (Refl _) ->
     *         ( UProveAll utac',
     *           ETac ( Gt_list jt,
     *                  Gt_unit,
     *                  ProveAll tac) )
     *       | None -> raise @@ fail_tac_type l_gt r_gt utac in
     *
     *   begin match l_gt with
     *     | Gt_top -> type_prove_all Gt_top
     *     | Gt_list jt -> type_prove_all jt
     *     | _ -> raise @@ fail_tac_type l_gt r_gt utac end *)

    | UOrElse (utac_l, utac_r) -> begin match tac_typ l_gt r_gt utac_l with
        | utac_l', ETac (l_gt, r_gt, _) -> match tac_typ l_gt r_gt utac_r with
          | utac_r', ETac (l_gt, r_gt, tac_r) ->
            let tac_l = check_type l_gt r_gt utac_l' in
            ( UOrElse (utac_l', utac_r'),
              ETac (l_gt, r_gt, OrElse (tac_l, tac_r))) end

    | UAndThen (utac_l, utac_r,_) ->
      let mid_gt = Gt_bot in
      begin match tac_typ l_gt mid_gt utac_l with
        | utac_l', ETac (l_gt, mid_gt, _) ->
          match tac_typ (bot_to_top mid_gt) r_gt utac_r with
          | utac_r', ETac (mid_gt, r_gt, tac_r) ->
            let tac_l = check_type l_gt (top_to_bot mid_gt) utac_l' in
            ( UAndThen (utac_l', utac_r', Some mid_gt),
              ETac (l_gt, r_gt, AndThen (tac_l, tac_r, mid_gt))) end

    (* | UPrint iutac -> begin match tac_typ l_gt r_gt iutac with
     *     | iutac', ETac (l_gt, r_gt, itac) ->
     *       ( UPrint iutac',
     *         ETac (l_gt, r_gt, TacPrint itac ) ) end *)


let tac_type : type a b. a gt -> b gt -> utac -> etac =
  fun l_gt r_gt utac -> snd @@ tac_typ l_gt r_gt utac

(* let rec list_to_and_then = function
 *   | [] -> raise @@ Failure "Empty proof"
 *   | a :: [] -> UPrint a
 *   | a :: rem -> UAndThen (UPrint a, list_to_and_then rem, None)
 *
 * let proof_type : type a b. a gt -> b gt -> utac list -> etac =
 *   fun l_gt r_gt utacs -> tac_type l_gt r_gt (list_to_and_then utacs) *)



(** Declare Goals And Proofs *)

type args = (string * Theory.kind) list

let make_goal ((uargs,uconstr), (eargs,econstr), ufact, efact) =
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

  { uvars = List.map snd uts_subst;
    uindices = List.map snd uindex_subst;
    uconstr = uconstr;
    ufact = ufact;
    postcond = [{ evars = List.map snd ets_subst;
                  eindices = List.map snd eindex_subst;
                  econstr = econstr;
                  efact = efact }] }



(** Right existential type for tactics. *)
type 'a ertac = ERTac : 'b gt * ('a,'b) tac -> 'a ertac

let parse_tactic : type a. a gt -> utac -> a ertac =
  fun gt utac -> match tac_type gt Gt_bot utac with
    | ETac (agt, bgt, tac) -> match get_refl gt agt with
      | None ->
        Log.log Log.LogTacticTC (fun () ->
            Fmt.epr "@[<v 0>The tactic @[%a@] is ill-typed.@;\
                     @[%a@] is incompatible with @[%a@]@;@]%!"
              pp_utac utac pp_gt gt pp_gt agt);
        raise Tactic_type_error

      | Some (Refl _) -> ERTac (bgt, tac)

(** Existential type for judgments. *)
type ejudgment = Ejudge : 'a gt * 'a judgment -> ejudgment


let remove_finished judges =
  List.filter (function Ejudge (gt,_) -> match get_refl gt Gt_unit with
      | None -> true
      | Some (Refl _) -> false) judges

let simplify judges =
  List.map (function Ejudge (gt,j) -> match get_refl gt Gt_postcond with
      | None -> Ejudge (gt,j)
      | Some (Refl _) ->
        if j.goal.eindices = [] && j.goal.evars = [] then
          Ejudge (Gt_fact, Judgment.set_goal j.goal.efact Gt_fact j)
        else Ejudge (gt,j)
    ) judges

(* State in proof mode. *)
let goals : formula list ref = ref []
let current_goal : formula option ref = ref None
let subgoals : ejudgment list ref = ref []
let goals_proved = ref []

let add_new_goal g = goals := g :: !goals

let iter_goals f = List.iter f !goals

let goals_to_proved () = !goals <> []

let start_proof () = match !current_goal, !goals with
  | None, goal :: _ ->
    assert (!subgoals = []);
    current_goal := Some goal;
    subgoals := [Ejudge (Gt_formula,Judgment.init goal)]
                |> simplify;
    None
  | Some _,_ ->
    Some "Cannot start a new proof (current proof is not done)."

  | _, [] ->
    Some "Cannot start a new proof (no goal remaining to prove)."

let is_proof_completed () = !subgoals = []

let complete_proof () =
  assert (is_proof_completed ());
  goals_proved := !current_goal :: !goals_proved;
  current_goal := None;
  subgoals := [];;

let pp_goal ppf () = match !current_goal, !subgoals with
  | None,[] -> assert false
  | Some _, [] -> Fmt.pf ppf "@[<v 0>[goal> No subgoals remaining.@]@."
  | Some _, (Ejudge (gt, j)) :: _ ->
    Fmt.pf ppf "@[<v 0>[goal> Focused goal (1/%d):@;%a@;@]"
      (List.length !subgoals)
      (Judgment.pp_judgment (pp_gt_el gt)) j
  | _ -> assert false

exception Tactic_failed of string


(** [eval_tactic_focus utac] tries to prove the focused subgoal using [utac].
    Return [true] if there are no subgoals remaining. *)
let eval_tactic_focus : utac -> bool = fun utac -> match !subgoals with
  | [] -> assert false
  | Ejudge (agt, judge) :: ejs' ->
    let failure_k () = raise @@ Tactic_failed "" in
    let suc_k judges _ =
      let ejs =
        List.fold_left (fun ejs judge ->
            Ejudge (judge.gt, judge) :: ejs
          ) ejs' judges
        |> remove_finished
        |> simplify in
      subgoals := ejs;
      is_proof_completed () in

    match parse_tactic agt utac with
    | ERTac (bgt, tac) ->
      tac_apply bgt tac judge suc_k failure_k

let cycle i l =
  let rec cyc acc i = function
    | [] -> raise @@ Tactic_failed "cycle error"
    | a :: l ->
      if i = 1 then l @ (List.rev (a :: acc))
      else cyc (a :: acc) (i - 1) l in

  if i = 0 then l else
  if i < 0 then cyc [] (List.length l + i) l
  else cyc [] i l

(** [eval_tactic utac] applies the tactic [utac].
    Return [true] if there are no subgoals remaining. *)
let eval_tactic : utac -> bool = fun utac -> match utac with
  | UCycle i -> subgoals := cycle i !subgoals; false
  | _ -> eval_tactic_focus utac

(** Tests *)

exception Tactic_type_ok

let test_tac_type : type a b. a gt -> b gt -> utac -> etac -> unit =
  fun l_gt r_gt utac etac -> match tac_type l_gt r_gt utac, etac with
    | ETac (a,b,tac), ETac (a',b',tac') ->
      match get_refl a a', get_refl b b' with
      | Some (Refl _), Some (Refl _) ->
        if tac = tac' then raise Tactic_type_ok
        else begin
          Log.log Log.LogTacticTC (fun () ->
              Fmt.epr "@[<v 0>The two following tactics are not equal:@;\
                       @[%a@]@;%a@;\
                       @[%a@]@;%a@;@]%!"
                pp_tac tac
                pp_tact_type (a,b)
                pp_tac tac'
                pp_tact_type (a',b'));
          raise Tactic_type_error end

      | None, _ | _, None ->
        Log.log Log.LogTacticTC (fun () ->
            Fmt.epr "@[<v 0>Eqrefl fails on the following tactics:@;\
                     @[%a@]@;%a@;\
                     @[%a@]@;%a@;@]%!"
              pp_tac tac
              pp_tact_type (a,b)
              pp_tac tac'
              pp_tact_type (a',b'));
        raise Tactic_type_error

let () =
  Checks.add_suite "Logic" [
    "Tactic type-checking", `Quick,
    begin fun () ->
      Alcotest.check_raises "Simple 0" Tactic_type_ok
        (fun () ->
           test_tac_type Gt_fact Gt_unit UAdmit
             ( ETac (Gt_fact, Gt_unit, Admit) ));

      Alcotest.check_raises "Simple 1" Tactic_type_ok
        (fun () -> test_tac_type Gt_postcond (Gt_unit) UAdmit
            ( ETac (Gt_postcond, Gt_unit, Admit) ));

      Alcotest.check_raises "Simple 2" Tactic_type_ok
        (fun () ->
           test_tac_type
             Gt_postcond
             (Gt_unit) UGammaAbsurd
             ( ETac ( Gt_postcond,
                      Gt_unit, GammaAbsurd ) ));

      Alcotest.check_raises "AndThen" Tactic_type_ok
        (fun () ->
           test_tac_type
             Gt_fact
             Gt_fact (UAndThen (USplit,UEqNames,None))
             ( ETac ( Gt_fact, Gt_fact,
                      AndThen (Split,EqNames,Gt_fact) )));

      Alcotest.check_raises "OrElse" Tactic_type_ok
        (fun () ->
           test_tac_type
             Gt_fact Gt_unit
             (UOrElse
                ( UAndThen (UIntro, UGammaAbsurd, None),
                  UConstrAbsurd ))
             ( ETac ( Gt_fact,
                      Gt_unit,
                      OrElse
                        ( AndThen (Intro, GammaAbsurd, Gt_fact),
                          ConstrAbsurd ))));

      Alcotest.check_raises "Simple fail 0" Tactic_type_error
        (fun () -> test_tac_type (Gt_postcond) (Gt_unit) UAdmit
            ( ETac (Gt_fact, Gt_unit, Admit) ));

      Alcotest.check_raises "Simple fail 1" Tactic_type_error
        (fun () ->
           test_tac_type
             Gt_fact
             (Gt_fact) UGammaAbsurd
             ( ETac ( Gt_fact,
                      Gt_unit, GammaAbsurd ) ));

    end
  ]

(* let () =
 *   Checks.add_suite "Logic" [
 *     "Empty", `Quick,
 *     begin fun () -> ()
 *     end
 *   ] *)
