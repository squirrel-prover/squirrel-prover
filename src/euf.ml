(** {2 SSCs checking} *)

open Utils
    
(** Internal exception *)
exception Bad_ssc_

(** Iterate on terms, raise Bad_ssc if the hash key occurs other than
  * in key position or if a message variable is used.
  *
  * We use the inexact version of [iter_approx_macros]: it allows
  * some macros to be undefined, though such instaces will not be
  * supported when collecting hashes; more importantly, it avoids
  * inspecting each of the multiple expansions of a same macro. *)
class check_key
    ~allow_vars ~allow_functions
    ~cntxt head_fn key_n = object (self)
                                  
  inherit Iter.iter_approx_macros ~exact:false ~cntxt as super
    
  method visit_message t = match t with
    | Term.Fun ((fn,_), _, [m;Term.Name _]) when fn = head_fn ->
      self#visit_message m
        
    | Term.Fun ((fn,_), _, [m1;m2;Term.Name _]) when fn = head_fn ->
      self#visit_message m1; self#visit_message m2
        
    | Term.Fun ((fn,_), _, [Term.Name _])
    | Term.Fun ((fn,_), _, [Term.Diff (Term.Name _, Term.Name _)])
    | Term.Fun ((fn,_), _, [_; Term.Name _])
    | Term.Fun ((fn,_), _, [_; Term.Diff (Term.Name _, Term.Name _)])
      when allow_functions fn -> ()
                                 
    | Term.Name n when n.s_symb = key_n -> raise Bad_ssc_
                                             
    | Term.Var m -> if not(allow_vars) then raise Bad_ssc_
          
    | _ -> super#visit_message t
end

(** Collect occurences of some function and key,
  * as in [Iter.get_f_messages] but ignoring boolean terms,
  * cf. Koutsos' PhD. *)
class get_f_messages ~fun_wrap_key ~drop_head ~cntxt head_fn key_n = object (self)
  inherit Iter.get_f_messages ~fun_wrap_key ~drop_head ~cntxt head_fn key_n as super
  method visit_message t =
    if Term.ty t = Type.Boolean then () else super#visit_message t
end

(*------------------------------------------------------------------*)
  
(*------------------------------------------------------------------*) 
(** Check the key syntactic side-condition in the given list of messages
  * and in the outputs, conditions and updates of all system actions:
  * [key_n] must appear only in key position of [head_fn].
  * Return unit on success, raise [Bad_ssc] otherwise. *)
let key_ssc
    ?(allow_vars=false) ?(messages=[]) ?(elems=[]) ~allow_functions
    ~cntxt head_fn key_n =
  let ssc =
    new check_key ~allow_vars ~allow_functions ~cntxt head_fn key_n
  in

  (* [e_case] is the error message to be thrown in case of error *)
  let check e_case t : Tactics.ssc_error option=
    try ssc#visit_message t; None
    with Bad_ssc_ -> Some (t, e_case)
  in
      
  let errors1 = List.filter_map (check E_message) messages in
  let errors2 = List.filter_map (check E_elem) elems in

  let errors3 =
    SystemExpr.fold_descrs 
      (fun descr acc ->
         let name = descr.name in

         let errors = 
           check (E_indirect (name, `Cond)) (snd descr.condition) ::
           check (E_indirect (name, `Output)) (snd descr.output) ::
           List.map (fun (update,t) ->
               check (E_indirect (name, `Update update.Term.s_symb)) t
             ) descr.updates in
         (List.filter_map (fun x -> x) errors) @ acc       
      ) cntxt.table cntxt.system []
  in
  errors1 @ errors2 @ errors3

(*------------------------------------------------------------------*)
(** [hashes_of_action_descr ~system action_descr head_fn key_n]
  * returns the list of pairs [is,m] such that [head_fn(m,key_n[is])]
  * occurs in [action_descr]. *)
let hashes_of_action_descr
     ?(drop_head=true) ~fun_wrap_key ~cntxt action_descr head_fn key_n =
  let iter = new get_f_messages ~fun_wrap_key ~drop_head ~cntxt head_fn key_n in
  iter#visit_message (snd action_descr.Action.output) ;
  List.iter (fun (_,m) -> iter#visit_message m) action_descr.Action.updates ;
  List.sort_uniq Stdlib.compare iter#get_occurrences

(*------------------------------------------------------------------*)
(** {2 Euf rules datatypes} *)

type euf_schema = {
  action_name  : Symbols.action Symbols.t;
  action       : Action.action;
  message      : Term.message;
  key_indices  : Vars.index list;
  env          : Vars.env;
}

let pp_euf_schema ppf case =
  Fmt.pf ppf "@[<v>@[<hv 2>*action:@ @[<hov>%a@]@]@;\
              @[<hv 2>*message:@ @[<hov>%a@]@]"
    Symbols.pp case.action_name
    Term.pp case.message

(** Type of a direct euf axiom case.
    [e] of type [euf_case] represents the fact that the message [e.m]
    has been hashed, and the key indices were [e.eindices]. *)
type euf_direct = { 
  d_key_indices : Vars.index list;
  d_message     : Term.message 
}

let pp_euf_direct ppf case =
  Fmt.pf ppf "@[<v>@[<hv 2>*key indices:@ @[<hov>%a@]@]@;\
              @[<hv 2>*message:@ @[<hov>%a@]@]"
    Vars.pp_list case.d_key_indices
    Term.pp case.d_message

type euf_rule = { hash : Term.fname;
                  key : Term.name;
                  case_schemata : euf_schema list;
                  cases_direct : euf_direct list }

let pp_euf_rule ppf rule =
  Fmt.pf ppf "@[<v>*hash: @[<hov>%a@]@;\
              *key: @[<hov>%a@]@;\
              *case schemata:@;<1;2>@[<v>%a@]@;\
              *direct cases:@;<1;2>@[<v>%a@]@]"
    Term.pp_fname rule.hash
    Term.pp_name rule.key
    (Fmt.list pp_euf_schema) rule.case_schemata
    (Fmt.list pp_euf_direct) rule.cases_direct

(*------------------------------------------------------------------*)
(** {2 Build the Euf rule} *)

let mk_rule ?(elems=[]) ?(drop_head=true) ~fun_wrap_key
    ~allow_functions ~cntxt ~env ~mess ~sign ~head_fn ~key_n ~key_is =

  let mk_of_hash action_descr (is,m) =
    (* Indices [key_is] from [env] must correspond to [is],
     * which contains indices from [action_descr.indices]
     * but also bound variables.
     *
     * Rather than refreshing all action indices, and generating
     * new variable names for bound variables, we avoid it in
     * simple cases: if a variable only occurs once in
     * [is] then the only equality constraint on it is that
     * it must be equal to the corresponding variable of [key_is],
     * hence we can replace it by that variable rather
     * than creating a new variable and an equality constraint.
     * This is not sound with multiple occurrences in [is] since
     * they induce equalities on the indices that pre-exist in
     * [key_is].
     *
     * We compute next the list [safe_is] of simple cases,
     * and the substitution for them. *)
    let env = ref env in

    let safe_is,subst_is =
      let multiple i =
        let n = List.length (List.filter ((=) i) is) in
        assert (n > 0) ;
        n > 1
      in
      List.fold_left2 (fun (safe_is,subst) i j ->
          if multiple i then safe_is,subst else
            i::safe_is,
            Term.(ESubst (mk_var i, mk_var j))::subst
        ) ([],[]) is key_is
    in

    (* Refresh action indices other than [safe_is] indices. *)
    let subst_fresh =
      List.map (fun i ->
          Term.(ESubst (mk_var i,
                        mk_var (Vars.fresh_r env i))))
        (List.filter
           (fun x -> not (List.mem x safe_is))
           action_descr.Action.indices)
    in

    (* Refresh bound variables from m and is, except those already
     * handled above. *)
    let subst_bv =
      (* Compute variables from m, add those from is
       * while preserving unique occurrences in the list. *)
      let vars = Term.get_vars m in
      let vars =
        List.fold_left (fun vars i ->
            if List.mem (Vars.EVar i) vars then vars else
              Vars.EVar i :: vars
          ) vars is
      in
      (* Remove already handled variables, create substitution. *)
      let index_not_seen i =
        not (List.mem i safe_is) &&
        not (List.mem i action_descr.Action.indices)
      in
      let not_seen = function
        | Vars.EVar v -> match Vars.ty v with
          | Type.Index -> index_not_seen v
          | _ -> true
      in

      let vars = List.filter not_seen vars in
      List.map
        (function Vars.EVar v ->
           Term.(ESubst (mk_var v,
                         mk_var (Vars.fresh_r env v))))
        vars
    in

    let subst = subst_fresh @ subst_is @ subst_bv in
    let action = Action.subst_action subst action_descr.action in
    { action_name = action_descr.name;     
      action;
      message = Term.subst subst m ;
      key_indices = List.map (Term.subst_var subst) is ; 
      env = !env }
  in
  
  (* TODO: we are using the less precise version of [fold_macro_support] *)
  let hash_cases =
    Iter.fold_macro_support1 (fun descr t hash_cases ->
        (* TODO: use get_f_messages_ext and use conditons to improve precision *)
        (* let fv = Vars.Sv.of_list1 descr.Action.indices in
         * let new_hashes =
         *   Iter.get_f_messages_ext
         *     ~fv ~fun_wrap_key ~drop_head ~cntxt head_fn key_n t
         * in *)

        let iter =
          new get_f_messages ~fun_wrap_key ~drop_head ~cntxt head_fn key_n
        in
        iter#visit_message t;
        let new_hashes = iter#get_occurrences in
        
        List.assoc_up_dflt descr [] (fun l -> new_hashes @ l) hash_cases
      ) cntxt env (mess :: sign :: elems) []
  in
  
  (* we keep only actions in which the name occurs *)
  let hash_cases =
    List.filter_map (fun (descr, occs) ->
        if occs = [] then None
        else Some (descr, List.sort_uniq Stdlib.compare occs)
      ) hash_cases
  in

  (* indirect cases *)
  let case_schemata =
    List.concat_map (fun (descr, hashes) ->
        List.map (mk_of_hash descr) hashes
      ) hash_cases
  in

  (* remove duplicate cases *)
  let case_schemata = List.fold_right (fun case acc ->
      (* FIXME: use a better redundancy check *)
      if List.mem case acc then acc else case :: acc
    ) case_schemata [] 
  in

  (* direct cases *)
  let cases_direct =
    let hashes =
      let iter =
        new get_f_messages ~fun_wrap_key ~drop_head ~cntxt head_fn key_n
      in
      iter#visit_message mess ;
      iter#visit_message sign ;
      List.iter iter#visit_message elems ;
      iter#get_occurrences
    in
    List.map
      (fun (d_key_indices,d_message) -> {d_key_indices;d_message})
      hashes
  in

  { hash          = head_fn;
    key           = key_n;
    case_schemata;
    cases_direct; }
