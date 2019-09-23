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

  val add_facts : gamma -> fact list -> gamma

  val get_facts : gamma -> fact list
  val set_facts : gamma -> fact list -> gamma

  val get_atoms : gamma -> atom list

  val update_trs : gamma -> gamma
    
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
                 trs : Completion.state option;
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

  let mk () = { facts = []; atoms = []; trs = None; actions_described = [] }

  let get_atoms g = List.map fst g.atoms
  
  (* We do not add atoms that are already a consequence of gamma. *)
  let add_atom g at =
    if List.mem at (get_atoms g) then g else
      begin
      let add at =  { g with atoms = (at, new_tag ()) :: g.atoms } in
      add at
        (* if !(g.trs) = None then add at else
          match at with
          | (Eq,s,t) ->
            if Completion.check_equalities (opt_get !(g.trs)) [s,t] then g
            else add at
          | (Neq,s,t) ->
            if Completion.check_disequalities (opt_get !(g.trs)) [s,t] then
              g
            else add at
           | _ -> add at (* TODO: do not add useless inequality atoms *) *)
      end
  let rec add_atoms g = function
    | [] -> { g with trs = None } 
    | at :: ats -> add_atoms (add_atom g at) ats

  (** [add_fact g f] adds [f] to [g]. We try some trivial simplification. *)
  let rec add_fact g = function
    | Atom at -> add_atom g at
    | Not (Atom at) ->  add_atom g (not_xpred at)
    | True -> g
    | And (f,f') -> add_fact (add_fact g f) f'
    | _ as f -> { g with facts = f :: g.facts }

  let rec add_facts g = function
    | [] -> { g with trs = None }
    | f :: fs -> add_facts (add_fact g f) fs

  let get_facts g = g.facts

  let set_facts g fs = add_facts { g with facts = []; trs = None} fs

  let get_eqs_neqs g =
     let eqs, _, neqs = List.map fst g.atoms
                       |> List.map norm_xatom
                       |> List.flatten
                       |> List.fold_left (fun acc (od,a,b) ->
                           add_xeq od (a,b) acc) ([],[],[]) in
     eqs,neqs

  let update_trs g =
    let eqs,_ = get_eqs_neqs g in
    let trs = Completion.complete eqs in
    {g with trs = Some trs}

  let get_trs g =
    opt_get g.trs
  (** [complete_gamma g] returns [None] if [g] is inconsistent, and [Some g']
      otherwise, where [g'] has been completed. *)
  let is_sat g =
    let g = update_trs g in
    let _, neqs = get_eqs_neqs g in
    Completion.check_disequalities (opt_get g.trs) neqs
         
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

  val is_valid : theta -> tatom list -> bool

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

  let is_valid theta (c:tatom list) =
    compute_models theta;
    Constr.query (opt_get !(theta.models)) c
 
  let get_equalities theta =
    compute_models theta;
    let ts = Term.constr_ts theta.constr |> List.sort_uniq Pervasives.compare in
    Constr.get_equalities (opt_get !(theta.models)) ts
  
end


type typed_goal =
  | Unit
  | Formula of formula
  | Postcond of postcond
  | Fact of fact

let pp_typed_goal fmt =
  function
  | Unit -> Fmt.pf fmt "unit"
  | Formula f -> pp_formula fmt f
  | Postcond p -> pp_postcond fmt p
  | Fact f -> pp_fact fmt f

let type_goal =
    function
  | Unit -> "unit"
  | Formula f -> "formula"
  | Postcond p -> "postcondition"
  | Fact f -> "fact"


exception Goal_type_error of string * string (* expected type and given type *)

module Judgment : sig
  (** Type of judgments:
      - [vars] and [indices] are the judgment free timestamp and index variables.
      - [theta.constr] constrains the judgment timestamp and index variables.
      - [theta.models] store the last minimal models of [theta.constr].
      - [gamma] is the judgment context.
      - [goal] contains the current goal, which is of type 'a. *)
  type judgment = private { vars : fvar list;
                               theta : Theta.theta;
                               gamma : Gamma.gamma;
                               goal : typed_goal; }

  val pp_judgment : Format.formatter -> judgment -> unit

  val init : formula -> judgment

  val add_vars : Term.fvar list -> judgment -> judgment
  val add_indices : Action.index list -> judgment -> judgment

  (** Side-effect: Add necessary action descriptions. *)
  val add_fact : Term.fact -> judgment -> judgment

  (** Side-effect: Add necessary action descriptions. *)
  val add_constr : Term.constr -> judgment -> judgment

  (** Side-effect: Add necessary action descriptions. *)
  val set_goal_fact : fact -> judgment -> judgment

  val update_trs : judgment -> judgment
  
  val set_goal : typed_goal -> judgment -> judgment

  val set_gamma : Gamma.gamma -> judgment ->  judgment

  val get_goal_fact : judgment -> fact

  val get_goal_formula : judgment -> formula

  val get_goal_postcond : judgment -> postcond
    
end = struct
  type judgment = { vars : fvar list;
                       theta : Theta.theta;
                       gamma : Gamma.gamma;
                       goal : typed_goal; }

  let pp_judgment ppf judge =
    let open Fmt in
    let open Utils in
    pf ppf "@[<v 0>%a@;\
           @[<v 0>%a@]\
            @[<hv 2>Theta:@ @[%a@]@]@;\
            @[%a@]@;\
            %a@;\
            %a@;@;@]"
      (fun ppf i -> (styled `Bold ident) ppf (String.make i '=')) 40
      (Term.pp_typed_fvars "") judge.vars
      Theta.pp_theta judge.theta
      Gamma.pp_gamma judge.gamma
      (fun ppf i -> (styled `Bold ident) ppf (String.make i '-')) 40
      pp_typed_goal judge.goal

  let init (goal : formula) =
    { vars = [];
      theta = Theta.mk Term.True;
      gamma = Gamma.mk ();
      goal = Formula goal;
      }

  let update_trs j =
    { j with gamma = Gamma.update_trs j.gamma }
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
        if List.mem i (get_indexvars j.vars) then j
        else { j with vars = (Term.IndexVar i) :: j.vars } in
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
    { j with gamma = Gamma.add_facts j.gamma [f] }

  let add_constr c j =
    let j = update_descr j (constr_actions c) in
    { j with theta = Theta.add_constr j.theta c }

  let set_goal_fact f j =
    let j = update_descr j (fact_actions f) in
    { j with goal = Fact f }

  let set_goal a j = { j with goal = a }

  let set_gamma g j = { j with gamma = g }

  let get_goal_fact j = match j.goal with  Fact f -> f | _ -> raise @@ Goal_type_error ("fact", type_goal j.goal)

  let get_goal_formula j = match j.goal with Formula f -> f | _ -> raise @@ Goal_type_error ("formula", type_goal j.goal)

  let get_goal_postcond j = match j.goal with Postcond p -> p | _ -> raise @@ Goal_type_error ("postcond", type_goal j.goal)
end

open Judgment

let remove_finished judges =
  List.filter (function j ->
    match j.goal with
    | Unit -> false
    | _ -> true)
    judges

let simplify =
 function j ->
    match j.goal with
   | Postcond p  when p.evars = [] -> Judgment.set_goal (Fact p.efact) j
   | Fact True -> Judgment.set_goal Unit j 
   | _ -> j

(** Current mode of the prover:
    - [InputDescr] : waiting for the process description.
    - [GoalMode] : waiting for the next goal.
    - [ProofMode] : proof of a goal in progress. *)
type prover_mode = InputDescr | GoalMode | ProofMode | WaitQed

(* State in proof mode. *)
type named_goal = string * formula
let goals : named_goal list ref = ref []
let current_goal : named_goal option ref = ref None
let subgoals : judgment list ref = ref []
let goals_proved = ref []

exception Cannot_undo

type proof_state = { goals : named_goal list;
                     current_goal : named_goal option;
                     subgoals : judgment list;
                     goals_proved : named_goal list;
                     cpt_tag : int;
                     prover_mode : prover_mode;
                   }

let parse_args goalname ts : subst =
  let goals = List.filter (fun (name,g) -> name = goalname) !goals_proved in
  match goals with
  | [] ->  raise @@ Failure "No proved goal with given name"
  | [(np,gp)] -> (
      let uvars = gp.uvars in
      if (List.length uvars) <> (List.length ts) then raise @@ Failure "Number of parameters different than expected";
      match !subgoals with
      | [] ->  raise @@ Failure "Cannot parse term with respect to empty current goal"
      |  j ::_ -> let u_subst = List.map (function
            IndexVar v -> Theory.Idx(Index.name v,v)
          | TSVar v -> Theory.TS(Tvar.name v,TVar v)
          | MessVar v -> Theory.Term(Mvar.name v,MVar v)) j.vars in
        List.map2 (fun t u -> match u,t with
            | TSVar a, t -> TS(TVar a, Theory.convert_ts u_subst t )                                                                           
            | MessVar a, t -> Term(MVar a, Theory.convert_glob u_subst t)

            | IndexVar a, Theory.Var iname -> Index(a, (Action.Index.get_or_make_fresh (Term.get_indexvars j.vars) iname))
            | _ ->  raise @@ Failure "Type error in the arguments"

          ) ts uvars
)
  | _ ->  raise @@ Failure "Multiple proved goals with same name"
              

(** Basic Tactics *)

let tact_wrap f v sk fk = sk (f v) fk

let tact_return a v = a v (fun r fk' -> r) (fun _ -> raise @@ Failure "return")

let tact_andthen a b sk fk v = a v (fun v fk' -> b v sk fk') fk

let tact_orelse a b sk fk v = a v sk (fun () -> b v sk fk)

let repeat t j sk fk =
  let rec success_loop oldj v fk' =
    match v with
    | [a] when a = oldj -> sk v fk
    | [b] -> t b (success_loop b) (fun _ -> sk v fk)
    | _ -> raise @@ Failure "cannot repeat a tactic creating subgoals"
  in
  t j (success_loop j) fk


let lift =
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

let goal_or_intro_l (judge : judgment) sk fk = match Judgment.get_goal_fact judge with
  | Or (lgoal, _) -> sk [set_goal_fact lgoal judge] fk
  | _ -> raise @@ Failure "goal ill-formed"

let goal_or_intro_r (judge : judgment) sk fk = match Judgment.get_goal_fact judge with
  | Or (_, rgoal) -> sk [set_goal_fact rgoal judge] fk
  | _ -> raise @@ Failure "goal ill-formed"

(** To prove phi \/ psi, try first to prove phi and then psi *)
let goal_or_intro (judge : judgment) sk fk =
  tact_orelse goal_or_intro_l goal_or_intro_r sk fk judge

let goal_true_intro (judge : judgment) sk fk = match Judgment.get_goal_fact judge with
  | True -> sk () fk
  | _ -> raise @@ Failure "goal ill-formed"

let goal_and_intro (judge : judgment) sk fk = match Judgment.get_goal_fact judge with
  | And (lgoal,rgoal) ->
    sk [ set_goal_fact lgoal judge;
         set_goal_fact rgoal judge ] fk
  | _ -> raise @@ Failure "goal ill-formed"
      
(** Introduce the universally quantified variables and the goal. *)
let goal_forall_intro (judge : judgment) sk fk =
  let jgoal = Judgment.get_goal_formula judge in
  let vsubst =List.fold_left (fun subst x -> if List.mem x judge.vars then (x,make_fresh_of_type x):: subst else (x,x)::subst ) [] jgoal.uvars in
  let subst = from_fvarsubst vsubst in
  let new_cnstr = subst_constr subst jgoal.uconstr
  and new_fact = subst_fact subst jgoal.ufact
  and new_goals =
    List.map (fun goal ->
        Postcond (subst_postcond subst goal)
      ) jgoal.postcond in
  let judges =
    List.map (fun goal ->
        Judgment.set_goal goal judge
        |> Judgment.add_vars @@ List.map snd vsubst
        |> Judgment.add_fact new_fact
        |> Judgment.add_constr new_cnstr
      ) new_goals in
  sk (List.map simplify judges) fk

(** [goal_exists_intro judge sk fk vnu inu] introduces the existentially
    quantified variables and the goal.
    [vnu] (resp. [inu]) is a mapping from the postcondition existentially binded
    timestamp (resp. index) variables to [judge.gamma] timestamp (resp. index)
    variables. *)
let goal_exists_intro (judge : judgment) sk fk nu=
  let jgoal = Judgment.get_goal_postcond judge in
  let pc_constr = subst_constr nu jgoal.econstr in
  let judge = set_goal (Fact (subst_fact nu jgoal.efact)) judge
              |> Judgment.add_constr (Not pc_constr) in
  sk [judge] fk

let goal_intro (judge : judgment) sk fk =
  match Judgment.get_goal_fact judge with
  | False -> sk [judge] fk
  | f -> let judge = Judgment.add_fact (Not (f)) judge
              |> set_goal_fact False in
    sk [judge] fk

let goal_any_intro (judge : judgment) sk fk =
  match judge.goal with
  | Formula _ -> goal_forall_intro judge sk fk
  | Fact _ -> goal_intro judge sk fk
  | _ -> fk ()

let fail_goal_false (judge : judgment) sk fk = match Judgment.get_goal_fact judge with
  | False -> fk ()
  | _ -> raise @@ Failure "goal ill-formed"

let constr_absurd (judge : judgment) sk fk =
  if not @@ Theta.is_sat judge.theta then
    sk [Judgment.set_goal Unit judge] fk
  else fk ()

let gamma_absurd (judge : judgment) sk fk =
  if not @@ Gamma.is_sat judge.gamma then
    sk [Judgment.set_goal Unit judge] fk
  else fk ()

let or_to_list f =
  let rec aux acc = function
    | Or (g,h) -> aux (aux acc g) h
    | _ as a -> a :: acc in

  (* Remark that we simplify the formula. *)
  aux [] (simpl_fact f)

let gamma_or_intro (judge : judgment) sk fk select_pred =
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
let eq_names (judge : judgment) sk fk =
  let judge = Judgment.update_trs judge in
  let cnstrs = Completion.name_index_cnstrs (Gamma.get_trs judge.gamma)
      (Gamma.get_all_terms judge.gamma) in
  let judge =
    List.fold_left (fun judge c ->
        Judgment.add_constr c judge
      ) judge cnstrs in
  sk [judge] fk

let eq_constants fn (judge : judgment) sk fk =
  let judge = Judgment.update_trs judge in  
  let cnstrs =
    Completion.constant_index_cnstrs fn (Gamma.get_trs judge.gamma)
      (Gamma.get_all_terms judge.gamma) in
  let judge =
    List.fold_left (fun judge c ->
        Judgment.add_constr c judge
      ) judge cnstrs in
  sk [judge] fk

let eq_timestamps (judge : judgment) sk fk =
  let ts_classes = Theta.get_equalities judge.theta
           |> List.map (List.sort_uniq Pervasives.compare)
  in
  let subst =
    let rec asubst e = function
        [] -> []
      | p::q -> TS(p,e):: (asubst e q) in
    List.map (function [] -> [] | p::q -> asubst p q) ts_classes |> List.flatten in 
  let terms = (Gamma.get_all_terms judge.gamma) in
  let facts = List.fold_left (fun acc t ->
      let normt =  subst_term subst t in
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

let euf_apply f_select (judge : judgment) sk fk =
  let g, at = Gamma.select judge.gamma f_select (set_euf true) in
  let judge = Judgment.set_gamma g judge in
  (* TODO: need to handle failure somewhere. *)
  sk (euf_apply_facts judge at) fk

let apply (gname:string) (subst:subst) (judge : judgment) sk fk =
  let goals = List.filter (fun (name,g) -> name = gname) !goals_proved in
    match goals with
    | [] ->  raise @@ Failure "No proved goal with given name"
    | [(np,gp)] ->
      (* we first check if constr is satisfied *)
      let new_constr =subst_constr subst gp.uconstr in
      let rec to_cnf c = match c with
        | Atom a -> [a]
        | True -> []
        | And (a,b) -> (to_cnf a)@(to_cnf b)
        | _ -> raise @@ Failure "Can only apply axiom with constraints restricted to conjunctions." in
      let tatom_list = to_cnf new_constr in
      if not( Theta.is_valid judge.theta tatom_list) then raise @@ Failure "Constraint on the variables not satisfied.";
      (* the precondition creates a new subgoal *)
      let new_judge =  Judgment.set_goal (Fact (subst_fact subst gp.ufact)) judge |> simplify  in
      let new_truths =
        List.map (fun goal ->
            subst_postcond subst goal
          ) gp.postcond in
      (* TODO : handle existential in axioms *)
      let judge =
        List.fold_left (fun judge nt ->
            Judgment.add_fact nt.efact judge
            |> Judgment.add_constr nt.econstr
          ) judge new_truths in 
      sk [new_judge; judge] fk
    | _ ->  raise @@ Failure "Multiple proved goals with same name"


(** Type for tacitcs. **)
type tac =
  | Admit : tac
  | Ident : tac

  | Left : tac
  | Right : tac
  | Intro : tac
  | Split : tac

  | Apply : (string * subst) -> tac

  | ForallIntro : tac
  | ExistsIntro : subst -> tac
  | AnyIntro : tac
      
  | GammaAbsurd : tac
  | ConstrAbsurd : tac

  | EqNames : tac
  | EqTimestamps : tac      
  | EqConstants : fname -> tac

  (* | UProveAll : utac -> utac *)
  | AndThen : tac * tac -> tac
  | OrElse : tac * tac -> tac
  | Try : tac * tac -> tac
  | Repeat : tac -> tac

  | Euf : int -> tac
  | Cycle : int -> tac

let rec pp_tac : Format.formatter -> tac -> unit =
  fun ppf tac -> match tac with
    | Admit -> Fmt.pf ppf "admit"
    | Ident -> Fmt.pf ppf "ident"

    | Left -> Fmt.pf ppf "goal_or_intro_l"
    | Right -> Fmt.pf ppf "goal_or_intro_r"
    | Intro -> Fmt.pf ppf "goal_intro"
    | Split -> Fmt.pf ppf "goal_and_intro"

    | Apply (s,t) -> Fmt.pf ppf "apply"

    | ForallIntro -> Fmt.pf ppf "forall_intro"
    | ExistsIntro (nu) ->
      Fmt.pf ppf "@[<v 2>exists_intro@;%a@]"
        pp_subst nu
    | AnyIntro -> Fmt.pf ppf "any_intro"
    | GammaAbsurd -> Fmt.pf ppf "gamma_absurd"
    | ConstrAbsurd -> Fmt.pf ppf "constr_absurd"

    | EqNames -> Fmt.pf ppf "eq_names"
    | EqTimestamps -> Fmt.pf ppf "eq_timestamps"                   
    | EqConstants fn -> Fmt.pf ppf "eq_constants %a" pp_fname fn

    (* | ProveAll utac -> Fmt.pf ppf "apply_all(@[%a@])" pp_tac utac *)
    | AndThen (ut, ut') ->
      Fmt.pf ppf "@[%a@]; @,@[%a@]" pp_tac ut pp_tac ut'
    | OrElse (ut, ut') ->
      Fmt.pf ppf "@[%a@] + @,@[%a@]" pp_tac ut pp_tac ut'
    | Try (ut, ut') ->
      Fmt.pf ppf "try@[%a@] orelse @,@[%a@]" pp_tac ut pp_tac ut'
    | Repeat t ->
      Fmt.pf ppf "repeat @[%a@]]" pp_tac t
    (* | TacPrint ut -> Fmt.pf ppf "@[%a@].@;" pp_tac ut *)

    | Euf i -> Fmt.pf ppf "euf %d" i
    | Cycle i -> Fmt.pf ppf "cycle %d" i

type 'a fk = unit -> 'a

type ('a,'b) sk = 'a -> 'b fk -> 'b

let rec tac_apply
 : type a.
  tac -> judgment ->
  (judgment list, a) sk ->
    a fk -> a =
  fun tac judge sk fk -> match tac with
    | Admit -> sk [Judgment.set_goal Unit judge] fk
    | Ident -> sk [judge] fk

    | ForallIntro -> goal_forall_intro judge sk fk
    | ExistsIntro (nu) -> goal_exists_intro judge sk fk nu
    | AnyIntro -> goal_any_intro judge sk fk
    | Apply (gname,s) -> apply gname s judge sk fk
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

    | AndThen (tac,tac') ->
      let suc_k judges sk fk =
        let exception Suc_fail in
        let compute_judges () =
          List.fold_left (fun acc judge ->
              let new_j =
                tac_apply tac' judge
                  (fun l _ -> l)
                  (fun () -> raise Suc_fail) in
              new_j @ acc
            ) [] judges in

        (* We catch the exception before calling the continuation. *)
        match compute_judges () with
        | j -> sk j fk
        | exception Suc_fail -> fk () in

      tact_andthen
        (tac_apply tac)
        suc_k
        sk fk judge

    | OrElse (tac,tac') ->
      tact_orelse (tac_apply tac) (tac_apply tac') sk fk judge

    | Try (tac,tac') ->
      tac_apply tac judge (fun _ fk -> sk [] fk)
        (fun () -> tac_apply tac' judge sk fk)
    | Repeat tac ->
      repeat (tac_apply tac) judge sk fk
    | Cycle _ -> assert false   (* This is not a focused tactic. *)

    (* | TacPrint tac ->
     *   Fmt.pr "%a @[<hov 0>%a@]@;%!"
     *     (Fmt.styled `Bold ident) "Tactic:" pp_tac tac;
     *   tac_apply gt tac judge (fun judge fk ->
     *       Fmt.pr "%a%!" (Judgment.pp_judgment (pp_gt_el gt)) judge;
     *       sk judge fk)
     *     fk *)

(** Declare Goals And Proofs *)

type args = (string * Theory.kind) list

let make_goal ((uargs,uconstr), (eargs,econstr), ufact, efact) =
  (* In the rest of this function, the lists need to be reversed and appended
     carefully to properly handle variable shadowing.  *)
  let (u_subst,ufvars) = Theory.convert_vars uargs
  and (e_subst,efvars) = Theory.convert_vars eargs in
  let uconstr =
    Theory.convert_constr_glob
      (List.rev uargs)
      u_subst
      uconstr in
  let ufact =
    Theory.convert_fact_glob
      u_subst
      ufact in

  let econstr =
    Theory.convert_constr_glob
      (List.rev_append eargs (List.rev uargs))
      (e_subst @ u_subst)
      econstr in
  let efact =
    Theory.convert_fact_glob
      (e_subst @ u_subst)
      efact in

  { uvars = ufvars;
    uconstr = uconstr;
    ufact = ufact;
    postcond = [{ evars = efvars;
                  econstr = econstr;
                  efact = efact }] }

type parsed_input =
    ParsedInputDescr
  | ParsedQed
  | ParsedTactic of tac
  | ParsedUndo of int
  | ParsedGoal of Goalmode.gm_input

let proof_states_history : proof_state list ref = ref []

let save_state mode =
  proof_states_history :=  {goals = !goals; current_goal = !current_goal; subgoals = !subgoals; goals_proved = !goals_proved; cpt_tag = !cpt_tag; prover_mode = mode }::(!proof_states_history)

let rec reset_state n =
  match (!proof_states_history,n) with
  | [],_ -> raise Cannot_undo
  | p::q,0 ->
    proof_states_history := q; 
    goals := p.goals;
    current_goal := p.current_goal;
    subgoals := p.subgoals;
    goals_proved := p.goals_proved;
    cpt_tag := p.cpt_tag;
    p.prover_mode
  | p::q, n -> proof_states_history := q; reset_state (n-1)
    
  
let add_new_goal g = goals := g :: !goals

let add_proved_goal g = goals_proved := g :: !goals_proved

let iter_goals f = List.iter f !goals

let goals_to_proved () = !goals <> []

let is_proof_completed () = !subgoals = []

exception Tactic_failed of string

let complete_proof () =
  assert (is_proof_completed ());
  try
    add_proved_goal (opt_get !current_goal);
    current_goal := None;
    subgoals := []
  with Not_found ->  raise (Tactic_failed "Cannot complete proof with empty current goal")

let pp_goal ppf () = match !current_goal, !subgoals with
  | None,[] -> assert false
  | Some _, [] -> Fmt.pf ppf "@[<v 0>[goal> No subgoals remaining.@]@."
  | Some _, j :: _ ->
    Fmt.pf ppf "@[<v 0>[goal> Focused goal (1/%d):@;%a@;@]"
      (List.length !subgoals)
      Judgment.pp_judgment j
  | _ -> assert false

exception Tactic_type_error of string


let simpGoal = AndThen(Repeat AnyIntro,
                       AndThen(EqNames,
                               AndThen(EqTimestamps,
                                       AndThen(Try(GammaAbsurd,Ident),
                                               Try(ConstrAbsurd,Ident))
                                      )
                              )
                      )
                    
let rec eval_tactic_judge : tac -> judgment -> judgment list = fun tac judge ->
   let failure_k () = raise @@ Tactic_failed (Fmt.strf "%a" pp_tac tac) in
   let suc_k judges _ =
     judges
   in
    try     
      tac_apply tac judge suc_k failure_k
    with Goal_type_error (expected,given)-> 
      raise @@ Tactic_type_error (Fmt.strf "@[The tactic %a is ill-typed, it was expected to be applied to a %s, not to a %s." pp_tac tac expected given)

let auto_simp judges =
  List.map simplify judges
  |> remove_finished
  |>  List.map (eval_tactic_judge simpGoal)
  |> List.flatten  
  |>  List.map simplify 
  |> remove_finished

(** [eval_tactic_focus utac] tries to prove the focused subgoal using [utac].
    Return [true] if there are no subgoals remaining. *)
let eval_tactic_focus : tac -> bool = fun tac -> match !subgoals with
  | [] -> assert false
  | judge :: ejs' -> 
    let ejs = (eval_tactic_judge tac judge) @ ejs'
              |> auto_simp
                 in
      subgoals := ejs;
      is_proof_completed ()

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
let eval_tactic : tac -> bool = fun utac -> match utac with
  | Cycle i -> subgoals := cycle i !subgoals; false
  | _ -> eval_tactic_focus utac


let start_proof () = match !current_goal, !goals with
  | None, (gname,goal) :: _ ->
    assert (!subgoals = []);
    cpt_tag := 0;
    current_goal := Some (gname,goal);
    subgoals := [Judgment.init goal]
                |> auto_simp
    ;
    None
  | Some _,_ ->
    Some "Cannot start a new proof (current proof is not done)."

  | _, [] ->
    Some "Cannot start a new proof (no goal remaining to prove)."
