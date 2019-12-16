(** Macro expansions *)

open Term

let is_defined name a =
  match Macro.get_def name with
    | Input -> false
    | Output | State _ ->
        (* We can expand the definitions of output@A and state@A
         * when A is an action name. We cannot do so for a variable
         * or a predecessor.
         * TODO generalize the approach so that we expand output@ts
         * when the judgment's constraints tell us that ts=A for some
         * name A. *)
        begin match a with
          | TName _ -> true
          | _ -> false
        end
    | Local _ -> true
    | Global (inputs,_,_,_) ->
        (* As for outputs and states, we can only expand on a name A,
         * because a global macro m(...)@A refer to inputs of A and
         * its sequential predecessors. *)
        begin match a with
          | TName l ->
              (* We could support |inputs| <= |l|,
               * but it is not clear that we'll ever need it,
               * because a global macro is really meant to be used
               * at a particular action name. *)
              List.length inputs = List.length l
          | _ -> false
        end

let get_definition name args a =
  match Macro.get_def name with
    | Input -> assert false
    | Output ->
       begin match a with
         | TName action -> snd Process.((get_action_descr action).output)
         | _ -> assert false
       end
    | State _ ->
       begin match a with
         | TName action ->
             let descr = Process.get_action_descr action in
               begin try
                 (* TODO rename indices *)
                 List.assoc (name,args) descr.Process.updates
               with Not_found ->
                 Term.Macro ((name,args), [], Term.TPred a)
               end
         | _ -> assert false
       end

    | Global (inputs,indices,ts,body) ->
        begin match a with
          | TName action when List.length inputs = List.length action ->
              let idx_subst =
                List.map2
                  (fun i i' -> Index (i,i'))
                  indices
                  args
              in
              let ts_subst = TS (TVar ts,a) in
              let subst,_ =
                List.fold_left
                  (fun (subst,action) x ->
                     let in_tm =
                       Macro (in_macro,[],
                              TName (List.rev action))
                     in
                     Term (MVar x,in_tm) :: subst,
                     List.tl action)
                  (ts_subst::idx_subst,List.rev action)
                  inputs
              in
              subst_term subst body
          | _ -> assert false
        end
    | Local _ -> assert false (* TODO *)

let get_dummy_definition mn indices =
  match Macro.get_def mn with
    | Global (inputs,indices,ts,term) ->
        let rec dummy_action k =
          if k = 0 then [] else
            { Action.par_choice = 0,[] ; sum_choice = 0,[] }
            :: dummy_action (k-1)
        in
        let dummy_action = dummy_action (List.length inputs) in
          get_definition mn indices (TName dummy_action)
    | _ -> assert false
