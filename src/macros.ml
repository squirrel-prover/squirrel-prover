(** Macro definitions *)

type Symbols.data +=
    Global_data of Vars.message list * Vars.index list * Vars.timestamp
                   * Term.message

let declare_global table name ~inputs ~indices ~ts t =
  let data = Global_data (inputs,indices,ts,t) in
  let def = Symbols.Global (List.length indices) in
    Symbols.Macro.declare table name ~data def

(** Macro expansions *)

open Term

let is_defined name a table =
  match Symbols.Macro.get_all name table with
    | Symbols.Input, _ -> false
    | Symbols.(Output | Cond | State _), _ ->
        (* We can expand the definitions of output@A and state@A
         * when A is an action name. We cannot do so for a variable
         * or a predecessor.
         * TODO generalize the approach so that we expand output@ts
         * when the judgment's constraints tell us that ts=A for some
         * name A. *)
        begin match a with
          | Action _ -> true
          | _ -> false
        end
    | Symbols.(Exec | Frame), _ ->
        begin match a with
          | Action _ | Init -> true
          | _ -> false
        end
    | Symbols.Local _, _ -> true
    | Symbols.Global _, Global_data (inputs,_,_,_) ->
        (* As for outputs and states, we can only expand on a name A,
         * because a global macro m(...)@A refer to inputs of A and
         * its sequential predecessors. *)
        begin match a with
          | Action (s,_) ->
              let action = snd (Action.of_symbol s table) in
              List.length inputs <= List.length action
          | _ -> false
        end
    | Symbols.Global _, _ -> assert false

let get_definition :
  type a.  SystemExpr.system_expr ->  Symbols.table -> 
  a Sorts.sort -> Symbols.macro Symbols.t ->
  Vars.index list -> Term.timestamp -> 
  a Term.term =
  fun se table sort name args a ->
  match sort with
  | Sorts.Message ->
    begin
      match Symbols.Macro.get_all name table with
      | Symbols.Input, _ -> assert false
      | Symbols.Output, _ ->
        begin match a with
          | Action (symb,indices) ->
            let action = Action.of_term symb indices table in
            snd SystemExpr.((descr_of_action table se action).Action.output)
          | _ -> assert false
        end
      | Symbols.Frame, _ ->
          begin match a with
            | Term.Init -> Term.Fun (f_zero,[])
            | Term.Action _ ->
                Term.Fun(Term.f_pair,
                  [Term.Macro ((name,sort,args), [], Term.Pred a);
                   Term.Fun (Term.f_pair,
                    [Term.boolToMessage (Term.Macro (Term.exec_macro, [], a));
                     Term.ITE(Term.Macro (Term.exec_macro, [], a),
                                          Term.Macro (Term.out_macro, [], a),
                                          Term.Fun(Term.f_zero,[]))])])
            | _ -> assert false
          end
      | Symbols.State _, _ ->
        begin match a with
          | Action (symb,indices) ->
            let action = Action.of_term symb indices table in
            let descr = SystemExpr.descr_of_action table se action in
            begin try
              (* Look for an update of the state macro [name] in the
              updates of [action] *)
              let ((n,s,is),msg) = List.find
                (fun ((n,s,is),_) ->
                  n = name && s = sort && List.length args = List.length is)
                descr.Action.updates
              in
                (* update found:
                - if indices [args] of the macro we want
                to expand are equal to indices [is] corresponding to this macro
                in the action description, then the macro expanded as defined
                by the update term
                - otherwise, we need to take into account the possibility that
                [arg] and [is] might be equal, and generate a conditional *)
                if args = is then msg
                else
                  Term.mk_ite
                    (Term.mk_indices_eq args is)
                    msg
                    (Term.Macro ((name,sort,args), [], Term.Pred a))
            with Not_found ->
              Term.Macro ((name,sort,args), [], Term.Pred a)
            end
          | _ -> assert false
        end
      | Symbols.Global _, Global_data (inputs,indices,ts,body) ->
        begin match a with
          | Action (tsymb,tidx) ->
            let action = Action.of_term tsymb tidx table in
            assert (List.length inputs <= List.length action) ;
            let idx_subst =
              List.map2
                (fun i i' -> Term.ESubst (Term.Var i,Term.Var i'))
                indices
                args
            in
            let ts_subst = Term.ESubst (Term.Var ts, a) in
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
                     Term.Macro (in_macro,[],
                                 SystemExpr.action_to_term table se
                                   (List.rev action))
                   in
                   Term.ESubst (Term.Var x,in_tm) :: subst,
                   List.tl action)
                (ts_subst::idx_subst,rev_action)
                inputs
            in
            let t = Term.subst subst body in
            begin
              let proj_t proj = Term.pi_term ~projection:proj t in
              (* The expansion of the body of the macro only depends on the
                 projections, not on the system names. *)
              match se with
              (* the body of the macro is expanded by projecting
                 according to the projection in case of single systems. *)
              | Single (s) -> proj_t (SystemExpr.get_proj s)
              (* For diff cases, if the system corresponds to a left and a right
                 projection of systems we can simply project the macro as is. *)
              | SimplePair _
              | Pair (Left _, Right _) -> proj_t None
              (* If we do not have a left and right projection, we must
                 reconstruct the body of the macros to have the correct
                 definition on each side. *)
              | Pair (s1, s2)  -> Term.Diff (proj_t (SystemExpr.get_proj s1),
                                             proj_t (SystemExpr.get_proj s2))
            end
          | _ -> assert false
        end
      | Symbols.Local _, _ -> failwith "Not implemented"
      |  _ -> assert false

    end
  | Sorts.Boolean ->
    begin
      match Symbols.Macro.get_all name table with
      | Symbols.Cond, _ ->
        begin match a with
          | Action (symb,indices) ->
            let action = Action.of_term symb indices table in
            let descr = SystemExpr.descr_of_action table se action in
            snd Action.(descr.condition)
          | _ -> assert false
        end
      | Symbols.Exec, _ ->
        begin match a with
          | Term.Init -> Term.True
          | Term.Action _ ->
            Term.And (Macro ((name, sort, args),[], Term.Pred a),
                      Macro (Term.cond_macro, [], a))
          | _ -> assert false
        end
      | _ -> assert false
    end
  | _ -> assert false

let get_dummy_definition :
  type a. SystemExpr.system_expr -> Symbols.table -> 
  a Sorts.sort -> Symbols.macro Symbols.t -> 
  Vars.index list -> 
  a Term.term =
  fun se table sort mn indices ->
  match Symbols.Macro.get_all mn table with
    | Symbols.(Global _, Global_data (inputs,indices,ts,term)) ->
      let dummy_action = System.dummy_action (List.length inputs) in
      let tdummy_action = SystemExpr.action_to_term table se dummy_action in
      get_definition se table sort mn indices tdummy_action
    | _ -> assert false
