open Utils
open Action
open Term

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
  (** Type of judgment contexts. We separate atoms from more complex facts.
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
         if (g.trs) = None then add at else
          match at with
          | (Eq,s,t) ->
            if Completion.check_equalities (opt_get g.trs) [s,t] then g
            else add at
          | (Neq,s,t) -> add at (* TODO : use a correct check_disequality *)
          | _ -> add at (* TODO: do not add useless inequality atoms *)
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

  let is_sat g =
    let g = update_trs g in
    let _, neqs = get_eqs_neqs g in
    Completion.check_disequalities (opt_get g.trs) neqs

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
    if List.mem d.action g.actions_described then g else

      (* Add this action and its consequences regarding
       * its condition, updates and output. *)
      let g = { g with actions_described = d.action :: g.actions_described } in
      let new_atoms =
        (Eq, Macro (out_macro, TName d.action), d.output) ::
        List.map
          (fun (s,t) ->
             (Eq, State (s, TName d.action), t))
          d.updates
      in
      let new_facts = [d.condition] in
      let g =
        add_facts
          (add_atoms g new_atoms)
          new_facts
      in

      (* Recursively add descriptions for the actions appearing
       * in the newly added items. *)
      let actions =
        (List.fold_left
           (fun lts fact ->
              List.rev_append lts (Term.fact_ts fact))
           (Term.atoms_ts new_atoms)
           new_facts)
        |> List.fold_left
             (fun acc ts -> match action_of_ts ts with
                | None -> acc
                | Some a -> a :: acc)
             [] in

      let descrs = List.map Process.get_descr actions in
      List.fold_left add_descr g descrs

  let get_all_terms g =
    let atoms = get_atoms g
    and facts = get_facts g in

    let all_atoms =
      List.fold_left (fun l f -> Term.atoms f @ l) atoms facts in
    List.fold_left (fun acc (_,a,b) -> a :: b :: acc) [] all_atoms

end

module Theta : sig
  type theta

  val pp_theta : Format.formatter -> theta -> unit

  val mk : constr -> theta

  val add_constr : theta -> constr -> theta

  val is_sat : theta -> bool

  val is_valid : theta -> tatom list -> bool

  val maximal_elems : theta -> timestamp list -> timestamp list

  val get_equalities : theta -> timestamp list list
end = struct
  open Constr

  type theta = { constr : constr;
                 models : models option;
                 models_is_exact : bool }

  let pp_theta ppf theta = Term.pp_constr ppf theta.constr

  let mk constr = { constr = constr;
                    models = None;
                    models_is_exact = false }

  let add_constr theta c =
    { theta with constr = Term.triv_eval (And(theta.constr, c));
                 models_is_exact = false }

  let compute_models theta =
    if (theta.models_is_exact) then theta
    else begin
      let models = Constr.models theta.constr in
      { theta with models = Some models;
                   models_is_exact = true}
    end

  let is_sat theta =
    let theta = compute_models theta in
    Constr.m_is_sat (opt_get theta.models)

  let maximal_elems theta tss =
    let theta = compute_models theta in
    Constr.maximal_elems (opt_get theta.models) tss

  let is_valid theta (c:tatom list) =
    let theta = compute_models theta in
    Constr.query (opt_get (theta.models)) c

  let get_equalities theta =
    let theta = compute_models theta in
    let ts = Term.constr_ts theta.constr
             |> List.sort_uniq Pervasives.compare
    in
    Constr.get_equalities (opt_get (theta.models)) ts

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

let type_goal = function
  | Unit -> "unit"
  | Formula f -> "formula"
  | Postcond p -> "postcondition"
  | Fact f -> "fact"


exception Goal_type_error of string * string (* expected type and given type *)

(** Judgments are the sequents of our proof system *)
module Judgment : sig
  (** Type of judgments:
      - [vars] and [indices] are the judgment free timestamp and index variables.
      - [theta.constr] constrains the judgment timestamp and index variables.
      - [theta.models] store the last minimal models of [theta.constr].
      - [gamma] is the judgment context.
      - [goal] contains the current goal, which is of type 'a. *)
  type judgment = { vars : fvar list;
                    theta : Theta.theta;
                    gamma : Gamma.gamma;
                    goal : typed_goal; }

  type t = judgment

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

  type t = judgment

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

  let get_vars j = j.vars

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

  let get_goal_fact j = match j.goal with
    | Fact f -> f
    | _ -> raise @@ Goal_type_error ("fact", type_goal j.goal)

  let get_goal_formula j = match j.goal with
    | Formula f -> f
    | _ -> raise @@ Goal_type_error ("formula", type_goal j.goal)

  let get_goal_postcond j = match j.goal with
    | Postcond p -> p
    | _ -> raise @@ Goal_type_error ("postcond", type_goal j.goal)

end
