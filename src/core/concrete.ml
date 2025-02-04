open Utils

include LowConcrete

(*------------------------------------------------------------------*)
let reduce_bound table system (s : bound) : bound =
  let state =
    Reduction.mk_state0
      ~system ~red_param:ReductionCore.rp_default ~concrete:true
      table
  in
  match s with
  | ReachAsym -> ReachAsym
  | ReachConc e ->
    let rede = Reduction.reduce_term state e in
    ReachConc rede
  | Glob -> Glob

(*------------------------------------------------------------------*)
type form_type =
  | Atom_conc of Term.term
  | Atom_asym
  | Form

(*------------------------------------------------------------------*)
let form_type_to_option ?(failure = true) (f : form_type) : Term.term option =
  match f with
  | Atom_asym -> None
  | Atom_conc c -> Some c
  | Form ->
    if failure then Tactics.soft_failure (Failure "not a atomic global goal");
    None

(*------------------------------------------------------------------*)
let global_extract_bound (g : Equiv.form) : form_type =
  match g with
  | Atom (Reach {bound = None})    -> Atom_asym
  | Atom (Reach {bound = Some ve}) -> Atom_conc ve
  | Atom (Equiv {bound = None})    -> Atom_asym
  | Atom (Equiv {bound = Some ve}) -> Atom_conc ve
  | _ -> Form

let global_set_bound  (e : Term.term) (g : Equiv.form) : Equiv.form =
  match g with
  | Atom (Reach {bound = None}) 
  | Atom (Equiv {bound = None}) -> Tactics.soft_failure (Failure "not a concrete goal")

  | Atom (Reach {formula; bound = Some _}) -> Atom (Reach {formula; bound = Some e})
  | Atom (Equiv {terms;   bound = Some _}) -> Atom (Equiv {terms;   bound = Some e})
  | _ -> Tactics.soft_failure (Failure "not a atomic global formula")

(*------------------------------------------------------------------*)
module BoundManagement (S : Sequent.S) = struct

  (*------------------------------------------------------------------*)
  let get_bound ?(failure = true) (s : S.t) : Term.term option =
    match S.conc_kind with
    | Equiv.Local_t -> to_option (S.bound s)
    | Equiv.Global_t ->
      form_type_to_option
        ~failure
        (global_extract_bound (S.conclusion s))
    | _ -> assert false

  (*------------------------------------------------------------------*)
  let conclusion_is_concrete (s : S.t) : bool =
    match S.conc_kind with
    | Equiv.Local_t -> LowConcrete.is_concrete (S.bound s)
    | Equiv.Global_t ->
      begin
        match S.conclusion s with
        | Atom (Reach {bound = Some _})
        | Atom (Equiv {bound = Some _}) -> true

        | _ -> false
      end
    | _ -> assert false

  (*------------------------------------------------------------------*)
  let conclusion_is_concrete_equiv (s : S.t) : bool =
    match S.conc_kind with
    | Equiv.Any_t -> assert false

    | Equiv.Local_t -> false

    | Equiv.Global_t ->
      match S.conclusion s with
      | Atom(Equiv e) when e.bound <> None -> true
      | _ -> false

  (*------------------------------------------------------------------*)
  let set_bound (e : Term.term) (s : S.t) :  S.t =
    assert (Type.equal Real.treal (Term.ty e));
    assert (conclusion_is_concrete s);

    match S.conc_kind with
    | Equiv.Local_t -> S.set_bound (ReachConc e) s

    | Equiv.Global_t ->
      begin
        match S.conclusion s with
        | Atom(Reach {formula; bound = Some _}) ->
          S.set_conclusion (Atom (Reach {formula; bound = Some e})) s

        | Atom(Equiv _) -> assert false (* FEAT: concrete logic for equivalences *)

        | _ -> assert false
      end

    | _ -> assert false

  (*------------------------------------------------------------------*)
  let do_bound (mode : [`Add | `Minus]) (b : Term.term) (s : S.t) : S.t =
    let system =
      if conclusion_is_concrete_equiv s then SE.context_any else S.system s
    in
    let state =
      Reduction.mk_state0
        ~hyps:(S.get_trace_hyps s)
        ~system ~red_param:ReductionCore.rp_default ~concrete:true
        (S.table s)
    in
    let b = Reduction.reduce_term state b in
    let g = get_bound ~failure:false s in
    let table = S.table s in
    match g with
    | None when Real.is_zero table b -> s

    | None -> Tactics.soft_failure (Failure "not a concrete goal")

    | Some _ when Real.is_zero table b -> s
    | Some goal_bound ->
      if not (Real.is_loaded table) then 
        Tactics.soft_failure (Failure "library Real is not loaded");

      let new_bound = 
        match mode with
        | `Add   -> Real.mk_add   ~simpl:true table goal_bound b 
        | `Minus -> Real.mk_minus ~simpl:true table goal_bound b 
      in
      set_bound new_bound s

  (*------------------------------------------------------------------*)
  (** see `.mli` *)
  let add_bound   (b : Term.term) (s : S.t) : S.t = do_bound `Add   b s

  (** see `.mli` *)
  let minus_bound (b : Term.term) (s : S.t) : S.t = do_bound `Minus b s

  (*------------------------------------------------------------------*)
  (** see `.mli` *)
  let leq_bound (new_bound : Term.term) (s : S.t) : S.t =
    match S.bound s with
    | ReachConc bound ->
      begin
        let table = S.table s in
        let z_r = ReachConc (Real.mk_zero table) in
        let c = Term.mk_leq new_bound bound in
        (* In the proof of the inequality, we cannot keep the
           local hypotheses. *)
        let s_leq = 
          S.Hyps.filter
            (fun (_,y) -> match S.hyp_kind with
               | Local_t | Global_t -> assert false
               | Any_t -> match y with
                 | LHyp (Local _) -> false
                 | LHyp (Global _) | LDef _ -> true)
            s 
        in
        match S.conc_kind with
        | Equiv.Local_t -> S.set_bound z_r (S.set_conclusion c s_leq)
        | _ -> assert false
      end
    | _ -> assert false

  (*------------------------------------------------------------------*)
  let list_bounds_fill
      (bounds : Term.t option list) (cases : 'a list) (s : S.t) 
    : bound list * S.t list
    =
    let table = S.table s in
    let bad_args ?(dbg="") () = 
      Tactics.hard_failure (Failure ("improper arguments" ^ dbg)) 
    in

    (*This function take either [] or [None,..,None] for bounds
      (representing respectively the case tactic without bounds arguments
      or a intro pattern without bound arguments)
      and either replace the None with conc or
      create a list of length m with conc in it.*)
    let fill  (m : int) conc bounds =
      if List.length bounds = 0 then
        List.init m (fun _ -> conc)
      else
        begin
          assert(m = List.length bounds);
          List.map (omap_dflt conc (fun _ -> bad_args ())) bounds
        end
    in

    let bounds_len = List.length bounds in
    let cases_len = List.length cases in

    (* Here we compute the [bounds] of the various sub-goals in cases.
       Depending on the number of user provided bounds, we need to add
       an additional goal [last_goal]
       (that the sum of all the bound given by the adversary is smaller
       than bound of the original conclusion). *)
    match S.bound s with
    | ReachAsym ->
      (* In the case of an asymptotic goal, we don't want any user
         provided bounds. *)
      fill cases_len ReachAsym bounds, []

    | Glob ->
      (* In the case of an asymptotic goal, we don't want any user
         provided bounds and for now, we only support asymptotic
         global logic.
          FEAT:Concrete: Maybe for some global tactics,
         something will have to be done here in order to make it either to distribute the bounds *)
      fill cases_len Glob bounds, []

    | ReachConc e as se->
      begin
        (* We compute the number of bound the user left blank. *)
        let filter_bounds  = List.filter_map (fun x -> x) bounds in
        let nb_bounds = cases_len - List.length filter_bounds in
        (* Create the sequent that ask to prove exactly that the sum
           of the user provided bounds is smaller that bound of the
           original conclusion. *)
        let z_r = ReachConc (Real.mk_zero table) in
        let sum =
          if List.length filter_bounds = 0 then None else
            Some (List.fold_left
                    (fun x -> fun y -> Real.mk_add table x y)
                    (List.hd filter_bounds)
                    (List.tl filter_bounds))
        in
        let comp =
          if List.length filter_bounds = 0 then [] else 
            begin
              let c = Term.mk_leq (oget sum) e in
              (* In the proof of the inequality, we cannot keep the
                 local hypothesis. *)
              (* FEAT:Concrete: Maybe try to keep more hypothesis here, just like in to_gobal_sequent.
                to_global_sequent is not used here since it change the form S.t to ES.t, which is annoying*)
              let s_leq = 
                S.Hyps.filter
                  (fun (_,y) -> match S.hyp_kind with
                     | Local_t -> assert false
                     | Global_t -> assert false
                     | Any_t -> match y with
                       | LHyp (Local _) -> false
                       | LHyp (Global _) -> true
                       | LDef _ -> false)
                  s in
              match S.conc_kind with
              | Equiv.Local_t -> [S.set_bound z_r (S.set_conclusion c s_leq)]
              | _ -> assert false
            end
        in
        let is_z_or_none =
          function
          | Some x when Real.is_zero table x -> true
          | None -> true
          | _ -> false
        in
        (* Compute the bound to put where user at left if blank, and
           if it require the additional proof. *)
        let h, bound_proof =
          match se, nb_bounds with
          | se, 0 when is_zero table se -> z_r, []
          | se, _ when is_zero table se && List.for_all is_z_or_none bounds -> z_r, comp
          | _, 0 -> z_r, comp
          | _, n ->
            let div =
              if sum <> None then
                if n = 1 then
                  Real.mk_minus table e (oget sum)
                else
                  Real.mk_div
                    table
                    (Real.mk_minus table e (oget sum))
                    (Real.mk_of_int table (Term.mk_int (Z.of_int n)))
              else
                Real.mk_div
                  table
                  e
                  (Real.mk_of_int table (Term.mk_int (Z.of_int n)))
            in
            ReachConc div, []
        in
        let bounds =
          if bounds_len > cases_len then
            bad_args ()
          else
            bounds @ 
            (List.init (cases_len - bounds_len) (fun _ -> None)) 
        in
        let complete_bounds =
          List.map
            (fun x ->
               match x with
               | Some x -> ReachConc x
               | None -> h
            ) bounds
        in
        assert (List.length bound_proof < 2);
        assert (List.length complete_bounds = cases_len);
        complete_bounds, bound_proof
      end

end
