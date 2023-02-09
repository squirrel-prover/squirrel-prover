(* DEPRECATED should no longer be used *)
(** {2 SSCs checking} *)

open Utils
    
(** Internal exception *)
exception Bad_ssc_

(** Iterate on terms, raise Bad_ssc if the hash key occurs other than
    in key position or if a message variable is used.
  
    We use the inexact version of [deprecated_iter_approx_macros]: it allows
    some macros to be undefined, though such instaces will not be
    supported when collecting hashes; more importantly, it avoids
    inspecting each of the multiple expansions of a same macro. *)
class check_key
    ~allow_functions
    ~cntxt head_fn key_n = object (self)

  inherit Iter.deprecated_iter_approx_macros ~exact:false ~cntxt as super

  method visit_message t = match t with
    | Term.Fun (fn, _, [Tuple [m;Term.Name _]]) when fn = head_fn ->
      self#visit_message m

    | Term.Fun (fn, _, [Tuple [m1;m2;Term.Name _]]) when fn = head_fn ->
      self#visit_message m1; self#visit_message m2

    | Term.Fun (fn, _, [Tuple [_;k]])
      when allow_functions fn && Term.diff_names k -> ()
                                                      
    | Term.Fun (fn, _, [k])
      when allow_functions fn && Term.diff_names k -> ()

    | Term.Name (n, _) when n.s_symb = key_n -> raise Bad_ssc_

    | Term.Var m -> 
      let ty = Vars.ty m in
      if ty <> Type.tindex && ty <> Type.ttimestamp then
        raise Bad_ssc_;
      (* TODO: DET: check for ptime_deducible *)

    | _ -> super#visit_message t
end

(** Collect occurences of some function and key,
    as in [Iter.deprecated_get_f_messages] but ignoring boolean terms,
    cf. Koutsos' PhD. *)
class deprecated_get_f_messages ~fun_wrap_key ~drop_head ~cntxt head_fn key_n = 
  object (_self)

  inherit Iter.deprecated_get_f_messages
      ~fun_wrap_key ~drop_head ~cntxt head_fn key_n as super

  method visit_message t =
    if Term.ty t = Type.Boolean then () else super#visit_message t
end

(*------------------------------------------------------------------*)
let err_msg_of_msymb table a (ms : Symbols.macro) : Tactics.ssc_error_c =
  let k = 
    match Symbols.Macro.get_def ms table with
    | Symbols.Output   -> `Output
    | Symbols.Cond     -> `Cond
    | Symbols.Global _ -> `Global ms
    | Symbols.State _  -> `Update ms
    | _ -> assert false
  in
  Tactics.E_indirect (a,k)

(*------------------------------------------------------------------*) 
(** Check the key syntactic side-condition in the given list of messages
  * and in the outputs, conditions and updates of all system actions:
  * [key_n] must appear only in key position of [head_fn].
  * Return unit on success, raise [Bad_ssc] otherwise. *)
let key_ssc
    ~globals ?(messages=[]) ?(elems=[]) ~allow_functions
    ~cntxt head_fn key_n =
  let ssc =
    new check_key ~allow_functions ~cntxt head_fn key_n
  in

  (* [e_case] is the error message to be thrown in case of error *)
  let check e_case t : Tactics.ssc_error option=
    try ssc#visit_message t; None
    with Bad_ssc_ -> Some (t, e_case)
  in
      
  let errors1 = List.filter_map (check E_message) messages in
  let errors2 = List.filter_map (check E_elem) elems in

  let errors3 =
    SystemExpr.fold_descrs (fun descr acc ->
        let name = descr.name in
        Iter.fold_descr ~globals (fun ms _a_is _m_is _mdef t acc ->
            let err_msg = err_msg_of_msymb cntxt.table name ms in
            match check err_msg t with
            | None -> acc
            | Some x -> x :: acc
          ) cntxt.table cntxt.system descr acc
      ) cntxt.table cntxt.system []
  in
  errors1 @ errors2 @ errors3

(*------------------------------------------------------------------*)
(** {2 Euf rules datatypes} *)

type euf_schema = {
  action_name  : Symbols.action;
  action       : Action.action_v;
  message      : Term.term;
  key_indices  : Term.terms;
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
  d_key_indices : Term.terms;
  d_message     : Term.term 
}

let pp_euf_direct ppf case =
  Fmt.pf ppf "@[<v>@[<hv 2>*key indices:@ @[<hov>%a@]@]@;\
              @[<hv 2>*message:@ @[<hov>%a@]@]"
    (Fmt.list ~sep:Fmt.comma Term.pp) case.d_key_indices
    Term.pp case.d_message

type euf_rule = { 
  hash : Symbols.fname;
  key : Symbols.name * Term.terms ; (* k(t1, ..., tn) *)
  case_schemata : euf_schema list;
  cases_direct : euf_direct list 
}

let pp_euf_rule ppf rule =
  Fmt.pf ppf "@[<v>*hash: @[<hov>%a@]@;\
              *key: @[<hov>%a(%a)@]@;\
              *case schemata:@;<1;2>@[<v>%a@]@;\
              *direct cases:@;<1;2>@[<v>%a@]@]"
    Term.pp_fname rule.hash
    Symbols.pp (fst rule.key) 
    (Fmt.list ~sep:Fmt.comma Term.pp) (snd rule.key)
    (Fmt.list pp_euf_schema) rule.case_schemata
    (Fmt.list pp_euf_direct) rule.cases_direct

(*------------------------------------------------------------------*)
(** {2 Build the Euf rule} *)

(** Exported *)
let[@warning "-27"] mk_rule 
    ~elems ~drop_head ~fun_wrap_key
    ~allow_functions ~cntxt ~(env : Env.t) ~mess ~sign ~head_fn ~key_n ~key_is 
  =

  let mk_of_hash action_descr ((is,m) : Term.t list * Term.t) =
    (* Legacy refresh of variables, probably unnecessarily complex. *)
    let env = ref env.vars in

    (* Refresh action indices. *)
    let subst_fresh =
      List.map (fun i ->
          Term.(ESubst (mk_var i,
                        mk_var (Vars.make_approx_r env i (Vars.Tag.gtag)))))
        action_descr.Action.indices
    in

    (* Refresh bound variables from m and is, except those already
     * handled above. *)
    let subst_bv =
      (* Compute variables from m, add those from is
       * while preserving unique occurrences in the list. *)
      let vars = Term.get_vars m in
      let vars =
        List.fold_left (fun vars i ->
            if List.mem i vars then vars else i :: vars
          ) vars (Vars.Sv.elements (Term.fvs is))
      in
      (* Remove already handled variables, create substitution. *)
      let index_not_seen i =
        not (List.mem i action_descr.Action.indices)
      in
      let not_seen = fun v ->
        match Vars.ty v with
        | Type.Index -> index_not_seen v
        | _ -> true
      in

      let vars = List.filter not_seen vars in
      List.map
        (fun v ->
           Term.(ESubst (mk_var v,
                         mk_var (Vars.make_approx_r env v (Vars.Tag.gtag)))))
        vars
    in

    let subst = subst_fresh @ subst_bv in
    let action = Action.subst_action_v subst action_descr.action in
    { action_name = action_descr.name;     
      action;
      message = Term.subst subst m ;
      key_indices = List.map (Term.subst subst) is ; 
      env = !env }
  in
  
  (* TODO: we are using the less precise version of [fold_macro_support] *)
  let hash_cases =
    Iter.fold_macro_support1 (fun descr t hash_cases ->
        let iter =
          new deprecated_get_f_messages
            ~fun_wrap_key ~drop_head ~cntxt head_fn key_n
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
        new deprecated_get_f_messages
          ~fun_wrap_key ~drop_head ~cntxt head_fn key_n
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
    key           = (key_n, key_is);
    case_schemata;
    cases_direct; }
