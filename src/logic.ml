open Utils
open Action
open Term
open Bformula
open Formula

type tag = { t_euf : bool; id : int }

let new_tag id = { t_euf = false ; id = id }

let set_euf b t = { t with t_euf = b }

exception Not_atom

module Gamma : sig
  (** Type of judgment contexts. *)
  type gamma

  val pp_gamma : Format.formatter -> gamma -> unit

  val empty : gamma

  val add_facts : gamma -> fact list -> gamma

  val set_facts : gamma -> fact list -> gamma

  val get_atoms : gamma -> term_atom list

  (* Check if a fact is in gamma, as an atom. *)
  val mem : fact -> gamma -> bool

  val update_trs : gamma -> gamma

  val get_trs : gamma -> Completion.state

  val is_sat : gamma -> bool

  val is_valid : gamma -> term_atom list -> bool

  val select : gamma -> (term_atom -> tag -> bool)
    -> (tag -> tag) -> gamma * term_atom

  val add_action_descr : gamma -> Process.action_descr -> gamma

  val get_all_terms :gamma -> Term.term list

end = struct
  (** Type of judgment contexts. We separate atoms from more complex facts.
      We store in [trs] the state of the completion algorithm when it was last
      called on [atoms]. *)
  type gamma = { atoms : (term_atom * tag) list;
                 trs : Completion.state option;
                 actions_described : Action.action list;
                 cur_id : int }

  let pp_gamma ppf gamma =
    Fmt.pf ppf "@[<v 0>\
                @[<hov 2>Actions described:@ %a@]@;\
                @[<hv 0>Atoms:@ @[<v 0>%a@]@]@;"
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") Action.pp_action)
      gamma.actions_described
      (Fmt.list (fun ppf (at,t) ->
           Fmt.pf ppf "%d: %a" t.id pp_term_atom at)) (List.rev gamma.atoms)

  let empty = { atoms = []; trs = None; actions_described = []; cur_id = 0 }

  let get_atoms g = List.map fst g.atoms

  class iter_macros f = object (self)
    inherit Iter.iter as super
    method visit_term t =
      match t with
        | Macro (o,[],TName a) when o = Term.out_macro ->
            f t (snd (Process.get_action_descr a).output)
        | Macro ((m,is),[],a) ->
            if Term.Macro.is_defined m a then
              let def = Term.Macro.get_definition m is a in
                f t def ;
                self#visit_term def
        | t -> super#visit_term t
  end

  (* We do not add atoms that are already a consequence of gamma. *)
  let rec add_atom g at =
    if List.mem at (get_atoms g) then g else
      let macro_eqs : term_atom list ref = ref [] in
      let iter =
        new iter_macros
          (fun t t' -> macro_eqs := (Eq,t,t') :: !macro_eqs)
      in
      let () = iter#visit_fact (Atom at) in
      let add at =
        { g with
          cur_id = g.cur_id+1 ;
          atoms = (at, new_tag g.cur_id) :: g.atoms }
      in
      let g =
        if (g.trs) = None then add at else
          match at with
          | (Eq,s,t) ->
            if Completion.check_equalities (opt_get g.trs) [s,t] then g
            else add at
          | (Neq,s,t) -> add at (* TODO : use a correct check_disequality *)
          | _ -> add at (* TODO: do not add useless inequality atoms *)
      in
      add_atoms g !macro_eqs

  and add_atoms g = function
    | [] -> { g with trs = None }
    | at :: ats -> add_atoms (add_atom g at) ats

  (** [add_fact g f] adds [f] to [g]. We try some trivial simplification. *)
  let rec add_fact g at = match triv_eval at with
    | Atom at -> add_atom g at
    | Not (Atom at) -> add_atom g (not_xpred at)
    | True -> g
    | And (f,f') -> add_fact (add_fact g f) f'
    | _ -> raise Not_atom

  let rec add_facts g = function
    | [] -> { g with trs = None }
    | f :: fs -> add_facts (add_fact g f) fs

  let set_facts g fs = add_facts { g with trs = None } fs

  let mem f g = match f with
    | Bformula.Atom at -> List.exists (fun (at',_) -> at = at') g.atoms
    | _ -> false

  let get_eqs_neqs_at_list atl =
    List.map norm_xatom atl
    |> List.flatten
    |> List.fold_left (fun acc (od,a,b) ->
        add_xeq od (a,b) acc) ([],[],[])

  let get_eqs_neqs g =
     let eqs, _, neqs = get_eqs_neqs_at_list (List.map fst g.atoms) in
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

  let is_valid g term_atom_lists =
    let g = update_trs g in
    let eqs,_,neqs = get_eqs_neqs_at_list term_atom_lists in
    Completion.check_equalities (opt_get g.trs) eqs

  let select g f f_up =
    let rec aux acc = function
      | [] -> raise Not_found
      | (at, t) :: rem ->
        if f at t then
          ({ g with atoms = List.rev_append acc ((at, f_up t) :: rem) }, at)
        else aux ((at,t) :: acc) rem in

    aux [] g.atoms

  let rec add_action_descr g d =
    let open Process in
    if List.mem d.action g.actions_described then g else

      (* Add this action and its consequences regarding
       * its condition, updates and output. *)
      let g = { g with actions_described = d.action :: g.actions_described } in
      let g = add_facts g [snd d.condition] in
      (* Recursively add descriptions for the actions appearing
       * in the newly added item: they also happen in the trace.
       * TODO we could immediately add all the actions that depend
       * sequentially on our action *)
      let actions =
        fact_ts (snd d.condition)
        |> List.fold_left
             (fun acc ts -> match action_of_ts ts with
                | None -> acc
                | Some a -> a :: acc)
             [] in

      let action_descrs = List.map Process.get_action_descr actions in
      List.fold_left add_action_descr g action_descrs

  let get_all_terms g =
    let atoms = get_atoms g in
    List.fold_left (fun acc (_,a,b) -> a :: b :: acc) [] atoms

end

module Theta : sig
  type theta

  val pp_theta : Format.formatter -> theta -> unit

  val mk : constr -> theta

  val add_constr : theta -> constr -> theta

  val is_sat : theta -> bool

  val is_valid : theta -> constr_atom list -> bool

  val maximal_elems : theta -> timestamp list -> timestamp list

  val get_equalities : theta -> timestamp list list
end = struct
  open Constr

  type theta = { constr : constr;
                 models : models option;
                 models_is_exact : bool }

  let pp_theta ppf theta = pp_constr ppf theta.constr

  let mk constr = { constr = constr;
                    models = None;
                    models_is_exact = false }

  let add_constr theta c =
    { theta with constr = triv_eval (And(theta.constr, c));
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

  let is_valid theta (c:constr_atom list) =
    let theta = compute_models theta in
    Constr.query (opt_get (theta.models)) c

  let get_equalities theta =
    let theta = compute_models theta in
    let ts = constr_ts theta.constr
             |> List.sort_uniq Pervasives.compare
    in
    Constr.get_equalities (opt_get (theta.models)) ts

end

exception Goal_type_error of string * string (* expected type and given type *)

module Judgment : sig
  (** Type of judgments:
      - [vars] and [indices] are the judgment free timestamp and index variables.
      - [theta.constr] constrains the judgment timestamp and index variables.
      - [theta.models] store the last minimal models of [theta.constr].
      - [gamma] is the judgment context.
      - [goal] contains the current goal, which is of type 'a. *)
  type judgment = private {
    env : Vars.env;
    theta : Theta.theta;
    gamma : Gamma.gamma;
    formula : formula;
  }

  type t = judgment

  val pp_judgment : Format.formatter -> judgment -> unit

  val init : formula -> judgment

  val add_fact : fact -> judgment -> judgment

  val add_happens : timestamp -> judgment -> judgment

  val add_constr : constr -> judgment -> judgment

  val add_atoms :
    fact list * constr list * timestamp list -> judgment -> judgment

  val mem_fact : fact -> judgment -> bool

  val update_trs : judgment -> judgment

  val set_env : Vars.env -> judgment -> judgment

  val set_formula : formula -> judgment -> judgment

  val set_gamma : Gamma.gamma -> judgment ->  judgment

end = struct
  type judgment = {
    env : Vars.env;
    theta : Theta.theta;
    gamma : Gamma.gamma;
    formula : formula;
  }

  type t = judgment

  let pp_judgment ppf judge =
    let open Fmt in
    let open Utils in
    pf ppf "@[<v 0>%a@;\
           @[<v 0>%a@]\
            @[<hv 2>Theta:@ @[%a@]@]@;\
            @[%a@]@;\
            %a@.\
            %a@;@;@]"
      (fun ppf i -> (styled `Bold ident) ppf (String.make i '=')) 40
      (Vars.pp_typed_env) judge.env
      Theta.pp_theta judge.theta
      Gamma.pp_gamma judge.gamma
      (fun ppf i -> (styled `Bold ident) ppf (String.make i '-')) 40
      pp_formula judge.formula

  let init (goal : formula) =
    { env = Vars.empty_env;
      theta = Theta.mk Bformula.True;
      gamma = Gamma.empty;
      formula = goal;
      }

  let update_trs j =
    { j with gamma = Gamma.update_trs j.gamma }

  let constr_actions c =
    constr_ts c
    |> List.fold_left (fun acc ts -> match action_of_ts ts with
        | None -> acc
        | Some a -> a :: acc
      ) []

  let update_descr j actions =
    let descrs = List.map Process.get_action_descr actions in
    let g = List.fold_left Gamma.add_action_descr j.gamma descrs in
    { j with gamma = g }

  let add_fact f j =
    { j with gamma = Gamma.add_facts j.gamma [f] }

  let mem_fact f j = Gamma.mem f j.gamma

  let add_constr c j =
    { j with theta = Theta.add_constr j.theta c }

  let add_happens h j =
    match h with
      | TName a -> update_descr j [a]
      | _ -> assert false (* TODO unsupported until judgments redesign *)

  let add_atoms (facts,constrs,happens) judge =
    List.fold_left (fun j f -> add_fact f j)
      (List.fold_left (fun j c -> add_constr c j)
         (List.fold_left (fun j h -> add_happens h j)
            judge
            happens)
         constrs)
      facts

  let set_env a j = { j with env = a }

  let set_formula a j = { j with formula = a }

  let set_gamma g j = { j with gamma = g }

end
