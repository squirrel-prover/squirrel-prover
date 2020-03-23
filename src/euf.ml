(* Exception thrown when the axiom syntactic side-conditions do not hold. *)
exception Bad_ssc

(** Iterate on terms, raise Bad_ssc if the hash key occurs other than
  * in key position or if a message variable is used.
  *
  * We use the inexact version of [iter_approx_macros]: it allows
  * some macros to be undefined, though such instaces will not be
  * supported when collecting hashes; more importantly, it avoids
  * inspecting each of the multiple expansions of a same macro. *)
class check_hash_key ~system hash_fn key_n = object (self)
  inherit Iter.iter_approx_macros ~exact:false ~system as super
  method visit_message t = match t with
    | Term.Fun ((fn,_), [m;Term.Name _]) when fn = hash_fn ->
        self#visit_message m
    | Term.Name (n,_) when n = key_n -> raise Bad_ssc
    | Term.Var m -> raise Bad_ssc
    | _ -> super#visit_message t
end

(** Collect hashes for a given hash function and key.
  * We use the exact version of [iter_approx_macros], otherwise
  * we might obtain meaningless terms provided by [get_dummy_definition]. *)
class get_hashed_messages ~system hash_fn key_n = object (self)
  inherit Iter.iter_approx_macros ~exact:true ~system as super
  val mutable hashes : (Vars.index list * Term.message) list = []
  method get_hashes = hashes
  method visit_message = function
    | Term.Fun ((hash_fn',_), [m;k]) when hash_fn' = hash_fn ->
        begin match k with
          | Term.Name (key_n',is) ->
              if key_n' = key_n then hashes <- (is,m) :: hashes
          | _ -> ()
        end ;
        self#visit_message m ; self#visit_message k
    | Term.Var m -> raise Bad_ssc
    | m -> super#visit_message m
end

exception Found

(** Iterator that raises [Found] when a boolean macro is visited.
  * It relies on the inexact version of [iter_approx_macros] to avoid
  * expanding the same macro several times. *)
class no_cond ~system = object (self)
  inherit Iter.iter_approx_macros ~exact:false ~system as super
  method visit_message = function
    | Term.Macro ((mn,sort,is),[],a)
      when Symbols.Macro.get_def mn = Symbols.Frame -> raise Found
    | m -> super#visit_message m
  method visit_formula = function
    | Term.Macro _ -> raise Found
    | f -> super#visit_formula f
end

(** Check the key syntactic side-condition in the given list of messages
  * and in the outputs, conditions and updates of all system actions:
  * [key_n] must appear only in key position of [hash_fn].
  * Return unit on success, raise [Bad_ssc] otherwise. *)
let euf_key_ssc ~system hash_fn key_n messages =
  let ssc = new check_hash_key ~system hash_fn key_n in
  List.iter ssc#visit_message messages ;
  Action.(iter_descrs system
    (fun action_descr ->
       ssc#visit_formula (snd action_descr.condition) ;
       ssc#visit_message (snd action_descr.output) ;
       List.iter (fun (_,t) -> ssc#visit_message t) action_descr.updates))

(** Check that [cond] and [exec] macros do not appear in messages
  * and in the outputs and updates of all system actions. *)
let no_cond ~system messages =
  let iter = new no_cond ~system in
  try
    List.iter iter#visit_message messages ;
    Action.(iter_descrs system
      (fun action_descr ->
         iter#visit_message (snd action_descr.output) ;
         List.iter (fun (_,t) -> iter#visit_message t) action_descr.updates)) ;
    true
  with Found -> false

(** Same as [euf_key_ssc] but returning a boolean.
  * This is used in the collision tactic, which looks for all h(_,k)
  * such that k satisfies the SSC. *)
let hash_key_ssc ~system hash_fn key_n messages =
  try
    euf_key_ssc ~system hash_fn key_n messages;
    true
  with Bad_ssc -> false

(** [hashes_of_action_descr ~system ~cond action_descr hash_fn key_n]
    returns the pairs [is,m] such that [hash_fn(m,key_n[is])] occurs
    in an action description. The conditions of action descriptions are
    only considered if [cond]. *)
let hashes_of_action_descr ~system ~cond action_descr hash_fn key_n =
  let iter = new get_hashed_messages ~system hash_fn key_n in
  iter#visit_message (snd action_descr.Action.output) ;
  List.iter (fun (_,m) -> iter#visit_message m) action_descr.Action.updates ;
  if cond then iter#visit_formula (snd action_descr.Action.condition) ;
  List.sort_uniq Pervasives.compare iter#get_hashes

type euf_schema = { message : Term.message;
                    key_indices : Vars.index list;
                    action_descr : Action.descr;
                    env : Vars.env }

let pp_euf_schema ppf case =
  Fmt.pf ppf "@[<v>@[<hv 2>*action:@ @[<hov>%a@]@]@;\
              @[<hv 2>*message:@ @[<hov>%a@]@]"
    Action.pp_action case.action_descr.Action.action
    Term.pp case.message

(** Type of a direct euf axiom case.
    [e] of type [euf_case] represents the fact that the message [e.m]
    has been hashed, and the key indices were [e.eindices]. *)
type euf_direct = { d_key_indices : Vars.index list;
                    d_message : Term.message }

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

let mk_rule ~system ~env ~mess ~sign ~hash_fn ~key_n ~key_is =
  euf_key_ssc ~system hash_fn key_n [mess;sign];
  let cond = not (no_cond ~system [mess;sign]) in
  { hash = hash_fn;
    key = key_n;
    case_schemata =
      Utils.map_of_iter (Action.iter_descrs system)
        (fun action_descr ->
          let env = ref env in
          hashes_of_action_descr ~system ~cond action_descr hash_fn key_n
          |> List.map (fun (is,m) ->
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
            let safe_is,subst_is =
              let multiple i =
                let n = List.length (List.filter ((=) i) is) in
                  assert (n > 0) ;
                  n > 1
              in
              List.fold_left2
                (fun (safe_is,subst) i j ->
                   if multiple i then safe_is,subst else
                     i::safe_is,
                     Term.(ESubst (Var i, Var j))::subst)
                ([],[])
                is key_is
            in
            (* Refresh action indices other than [safe_is] indices. *)
            let subst_fresh =
              List.map
                (fun i ->
                   Term.(ESubst (Var i,
                                 Var (Vars.make_fresh_from_and_update env i))))
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
                List.fold_left
                  (fun vars i ->
                     if List.mem (Vars.EVar i) vars then vars else
                       Vars.EVar i :: vars)
                  vars
                  is
              in
              (* Remove already handled variables, create substitution. *)
              let index_not_seen i =
                not (List.mem i safe_is) &&
                not (List.mem i action_descr.Action.indices)
              in
              let not_seen = function
                | Vars.EVar ({Vars.var_type=Sorts.Index} as i) ->
                    index_not_seen i
                | _ -> true
              in
              let vars = List.filter not_seen vars in
              List.map
                (function Vars.EVar v ->
                   Term.(ESubst (Var v,
                                 Var (Vars.make_fresh_from_and_update env v))))
                vars
            in
            let subst = subst_fresh @ subst_is @ subst_bv in
            let new_action_descr = Action.subst_descr subst action_descr in
            { message = Term.subst subst m ;
              key_indices = List.map (Term.subst_var subst) is ;
              action_descr = new_action_descr;
              env = !env }))
      |> List.flatten;

    cases_direct =
      let hashes =
        let iter = new get_hashed_messages ~system hash_fn key_n in
        iter#visit_message mess ;
        iter#visit_message sign ;
        iter#get_hashes
      in
      List.map
        (fun (d_key_indices,d_message) -> {d_key_indices;d_message})
        hashes }
