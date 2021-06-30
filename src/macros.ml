open Utils

module SE = SystemExpr

(*------------------------------------------------------------------*)
(** {2 Macro definitions} *)

type Symbols.data +=
    Global_data of Vars.message list * Vars.index list * Vars.timestamp
                   * Term.message

let is_tuni = function Type.TUnivar _ -> true | _ -> false

let declare_global table name ~inputs ~indices ~ts t ty =
  assert (not (is_tuni ty));
  let data = Global_data (inputs,indices,ts,t) in
  let def = Symbols.Global (List.length indices, ty) in
    Symbols.Macro.declare table name ~data def

(*------------------------------------------------------------------*)
(** {2 Macro expansions} *)

let is_defined name a table =
  match Symbols.Macro.get_all name table with
    | Symbols.Input, _ -> false
    | Symbols.(Output | Cond | State _), _ ->
        (* We can expand the definitions of output@A and state@A
         * when A is an action name. We cannot do so for a variable
         * or a predecessor. *)
        begin match a with
          | Term.Action _ -> true
          | _ -> false
        end
    | Symbols.(Exec | Frame), _ ->
        begin match a with
          | Term.Action _ -> true
          | _ -> false
        end
    | Symbols.Global _, Global_data (inputs,_,_,_) ->
        (* As for outputs and states, we can only expand on a name A,
         * because a global macro m(...)@A refer to inputs of A and
         * its sequential predecessors. *)
        begin match a with
          | Term.Action (s,_) ->
              let action = snd (Action.of_symbol s table) in
              List.length inputs <= List.length action
          | _ -> false
        end
    | Symbols.Global _, _ -> assert false

(*------------------------------------------------------------------*)
let get_def 
    (system : SE.t)
    (table  : Symbols.table)
    (symb   : Term.msymb)
    (a      : Term.timestamp) : Term.message 
  =
  match Symbols.Macro.get_all symb.s_symb table with
  | Symbols.Input, _ -> assert false
  | Symbols.Output, _ ->
    let symb, indices = oget (Term.destr_action a) in
    let action = Action.of_term symb indices table in
    let descr = 
      SE.descr_of_action table system action 
    in
    snd descr.Action.output

  | Symbols.Cond, _ ->
    let symb, indices = oget (Term.destr_action a) in
    let action = Action.of_term symb indices table in
    let descr = 
      SE.descr_of_action table system action 
    in
    snd Action.(descr.condition)

  | Symbols.Exec, _ ->
    begin match a with
      | Term.Action (s,_) when s = Symbols.init_action -> Term.mk_true
      | Term.Action _ ->
        Term.mk_and
          (Term.mk_macro symb [] (Term.mk_pred a))
          (Term.mk_macro Term.cond_macro [] a)
      | _ -> assert false
    end

  | Symbols.Frame, _ ->
    begin match a with
      | Term.Action (s,_) when s = Symbols.init_action -> Term.mk_zero
      | Term.Action _ ->
        Term.mk_pair
          (Term.mk_macro symb [] (Term.mk_pred a))
          (Term.mk_pair
             (Term.mk_of_bool (Term.mk_macro Term.exec_macro [] a))
             (Term.mk_ite
                (Term.mk_macro Term.exec_macro [] a)
                (Term.mk_macro Term.out_macro [] a)
                Term.mk_zero))

      | _ -> assert false
    end

  | Symbols.State _, _ ->
    let asymb, indices = oget (Term.destr_action a) in
    let action = Action.of_term asymb indices table in
    let descr = SE.descr_of_action table system action in
    begin try
        (* Look for an update of the state macro [name] in the
           updates of [action] *)
        let (ns, msg) : Term.state * Term.message = 
          List.find (fun (ns,_) -> 
              ns.Term.s_symb = symb.s_symb && 
              List.length ns.Term.s_indices = List.length symb.s_indices
            ) descr.Action.updates
        in
        assert (ns.Term.s_typ = symb.s_typ);

        (* init case: we substitute the indice by their definition *)
        if a = Term.init then 
          let s = List.map2 (fun i1 i2 -> 
              Term.ESubst (Term.mk_var i1, Term.mk_var i2)
              ) ns.s_indices symb.s_indices
          in
          Term.subst s msg
          (* if indices [args] of the macro we want
             to expand are equal to indices [is] corresponding to this macro
             in the action description, then the macro expanded as defined
             by the update term *)
        else if symb.s_indices = ns.s_indices then msg
        (*  otherwise, we need to take into account the possibility that
            [arg] and [is] might be equal, and generate a conditional.  *)
        else
          Term.mk_ite
            (Term.mk_indices_eq symb.s_indices ns.s_indices)
            msg
            (Term.mk_macro symb [] (Term.mk_pred a))
      with Not_found ->
        Term.mk_macro symb [] (Term.mk_pred a)
    end

  | Symbols.Global _, Global_data (inputs,indices,ts,body) ->
    let tsymb, tidx = oget (Term.destr_action a) in
    let action = Action.of_term tsymb tidx table in
    assert (List.length inputs <= List.length action) ;
    let idx_subst =
      List.map2
        (fun i i' -> Term.ESubst (Term.mk_var i,Term.mk_var i'))
        indices
        symb.s_indices
    in
    let ts_subst = Term.ESubst (Term.mk_var ts, a) in
    (* Compute the relevant part of the action, i.e. the
         * prefix of length [length inputs], reversed. *)
    let rev_action =
      let rec drop n l = if n=0 then l else drop (n-1) (List.tl l) in
      drop (List.length action - List.length inputs) (List.rev action)
    in
    let subst,_ =
      List.fold_left
        (fun (subst,action) x ->
           let in_tm =
             Term.mk_macro 
               Term.in_macro []
               (SE.action_to_term table system (List.rev action))
           in
           Term.ESubst (Term.mk_var x,in_tm) :: subst,
           List.tl action)
        (ts_subst::idx_subst,rev_action)
        inputs
    in
    let t = Term.subst subst body in
    begin
      let proj_t proj = Term.pi_term ~projection:proj t in
      (* The expansion of the body of the macro only depends on the
         projections, not on the system names. *)
      match system with
      (* the body of the macro is expanded by projecting
         according to the projection in case of single systems. *)
      | Single (s) -> proj_t (SE.get_proj s)
      (* For diff cases, if the system corresponds to a left and a right
         projection of systems we can simply project the macro as is. *)
      | SimplePair _
      | Pair (Left _, Right _) -> proj_t PNone
      (* If we do not have a left and right projection, we must
         reconstruct the body of the macros to have the correct
         definition on each side. *)
      | Pair (s1, s2)  -> 
        Term.mk_diff (proj_t (SE.get_proj s1)) (proj_t (SE.get_proj s2))
    end

  |  _ -> assert false

(*------------------------------------------------------------------*)
let get_definition : 
  Constr.trace_cntxt -> Term.msymb -> Term.timestamp -> Term.message =
  fun cntxt symb ts ->
  let ts_action = 
    if is_defined symb.s_symb ts cntxt.table 
    then Some ts
    else match cntxt.models with
      | Some models -> Constr.find_eq_action models ts
      | None -> None
  in

  (* FIXME: we are throwing a tactic error there *)
  if ts_action = None then
    Tactics.soft_failure (Tactics.Failure "macro at undetermined action");
  
  let ts_action = Utils.oget ts_action in

  (* FIXME: idem + improve error message *)  
  if not (is_defined symb.s_symb ts_action cntxt.table) then 
    Tactics.soft_failure (Tactics.Failure "cannot expand this macro");

  let mdef = get_def cntxt.system cntxt.table symb ts_action in
  Term.subst [Term.ESubst (ts_action, ts)] mdef 

let get_definition_opt cntxt symb ts =
  try Some (get_definition cntxt symb ts) with
  | Tactics.Tactic_soft_failure _ -> None


(*------------------------------------------------------------------*)
let get_dummy_definition 
    (cntxt : Constr.trace_cntxt) 
    (symb : Term.msymb) : Term.message 
  =
  match Symbols.Macro.get_all symb.s_symb cntxt.table with
  | Symbols.(Global _, Global_data (inputs,indices,ts,term)) ->
    let dummy_action = Action.dummy (List.length inputs) in
    let tdummy_action = 
      SE.action_to_term cntxt.table cntxt.system dummy_action 
    in
    get_definition cntxt symb tdummy_action
  | _ -> assert false
