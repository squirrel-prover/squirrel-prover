(** Macro definitions *)

type Symbols.data +=
    Global_data of Vars.message list * Vars.index list * Vars.timestamp
                   * Term.message

let declare_global name ~inputs ~indices ~ts t =
  let data = Global_data (inputs,indices,ts,t) in
  let def = Symbols.Global (List.length indices) in
    Symbols.Macro.declare name ~data def

(** Macro expansions *)

open Term

let is_defined name a =
  match Symbols.Macro.get_all name with
    | Symbols.Input, _ -> false
    | Symbols.(Output | State _), _ ->
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
    | Symbols.Local _, _ -> true
    | Symbols.Global _, Global_data (inputs,_,_,_) ->
        (* As for outputs and states, we can only expand on a name A,
         * because a global macro m(...)@A refer to inputs of A and
         * its sequential predecessors. *)
        begin match a with
          | Action (s,_) ->
              let action = snd (Action.of_symbol s) in
              (* We could support |inputs| <= |action|,
               * but it is not clear that we'll ever need it,
               * because a global macro is really meant to be used
               * at a particular action name. *)
              List.length inputs = List.length action
          | _ -> false
        end
    | Symbols.Global _, _ -> assert false

let get_definition ~system_id name args a =
  match Symbols.Macro.get_all name with
    | Symbols.Input, _ -> assert false
    | Symbols.Output, _ ->
       begin match a with
         | Action (symb,indices) ->
             let action = Action.of_term symb indices in
             snd Action.((get_descr ~system_id action).output)
         | _ -> assert false
       end
    | Symbols.State _, _ ->
       begin match a with
         | Action (symb,indices) ->
             (* We are looking at name(args)@symb(indices):
              * see if state name(args) is updated by symb(indices),
              * otherwise its content is unchanged. *)
             let action = Action.of_term symb indices in
             let descr = Action.get_descr ~system_id action in
               begin try
                 List.assoc (name,args) descr.Action.updates
               with Not_found ->
                 Term.Macro ((name,args), [], Term.Pred a)
               end
         | _ -> assert false
       end
    | Symbols.Global _, Global_data (inputs,indices,ts,body) ->
        begin match a with
          | Action (tsymb,tidx) ->
              let action = Action.of_term tsymb tidx in
              assert (List.length inputs = List.length action) ;
              let idx_subst =
                List.map2
                  (fun i i' -> Term.ESubst (Term.Var i,Term.Var i'))
                  indices
                  args
              in
              let ts_subst = Term.ESubst (Term.Var ts, a) in
              let subst,_ =
                List.fold_left
                  (fun (subst,action) x ->
                     let in_tm =
                       Term.Macro (in_macro,[],
                                   Action.to_term (List.rev action))
                     in
                     Term.ESubst (Term.Var x,in_tm) :: subst,
                     List.tl action)
                  (ts_subst::idx_subst,List.rev action)
                  inputs
              in
              Term.subst subst body
          | _ -> assert false
        end
    | Symbols.Global _, _ -> assert false
    | Symbols.Local _, _ -> failwith "TODO"

let get_dummy_definition ~system_id mn indices =
  match Symbols.Macro.get_all mn with
    | Symbols.(Global _, Global_data (inputs,indices,ts,term)) ->
        let dummy_action = Action.dummy_action (List.length inputs) in
        get_definition ~system_id mn indices (Action.to_term dummy_action)
    | _ -> assert false
