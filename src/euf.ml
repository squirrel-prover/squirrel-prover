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
class get_hashed_messages ~system hash_fn key_n acc = object (self)
  inherit Iter.iter_approx_macros ~exact:true ~system as super
  val mutable hashes : (Vars.index list * Term.message) list = acc
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

(** [h_o_term hash_fn key_n acc t] adds to [acc] all pairs [is,m] such that
  * [hash_fn(m,key_n(is))] occurs in [t]. *)
let h_o_term ~system hash_fn key_n acc t =
  let iter = new get_hashed_messages ~system hash_fn key_n acc in
  iter#visit_message t ;
  iter#get_hashes

let h_o_formula ~system hash_fn key_n acc f =
  let iter = new get_hashed_messages ~system hash_fn key_n acc in
  iter#visit_formula f ;
  iter#get_hashes

(** [hashes_of_action_descr ~system ~cond action_descr hash_fn key_n]
    returns the pairs [is,m] such that [hash_fn(m,key_n[is])] occurs
    in an action description. The conditions of action descriptions are
    only considered if [cond]. *)
let hashes_of_action_descr ~system ~cond action_descr hash_fn key_n =
  let open Action in
  let hashes =
    List.fold_left (h_o_term ~system hash_fn key_n)
      [] (snd action_descr.output :: (List.map snd action_descr.updates))
  in
  let hashes =
    if cond then
      h_o_formula ~system hash_fn key_n hashes (snd action_descr.condition)
    else hashes
  in
  List.sort_uniq Pervasives.compare hashes

let hashes_of_term ~system term hash_fn key_n =
  h_o_term ~system hash_fn key_n [] term

type euf_schema = { message : Term.message;
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
            (* Replace key indices in hash by their value in goal. *)
            let subst_is =
              List.map2
                (fun i j -> Term.(ESubst (Var i, Var j)))
                is key_is
            in
            (* Refresh action indices other than key indices. *)
            let subst_fresh =
              List.map
                (fun i ->
                   Term.(ESubst (Var i,
                                 Var (Vars.make_fresh_from_and_update env i))))
                (List.filter
                   (fun x -> not (List.mem x is))
                   action_descr.Action.indices)
            in
            (* Generate new variables for remaining variables in hash,
             * which can come from internal bindings e.g. in universal
             * quantifications. *)
            let subst_bv =
              let not_seen = function
                | Vars.EVar ({Vars.var_type=Sorts.Index} as i) ->
                    not (List.mem i is) &&
                    not (List.mem i action_descr.Action.indices)
                | _ -> true
              in
              let vars = List.filter not_seen (Term.get_vars m) in
              List.map
                (function Vars.EVar v ->
                   Term.(ESubst (Var v,
                                 Var (Vars.make_fresh_from_and_update env v))))
                vars
            in
            let subst = subst_fresh @ subst_is @ subst_bv in
            let new_action_descr = Action.subst_descr subst action_descr in
            { message = Term.subst subst m ;
              action_descr = new_action_descr;
              env = !env }))
      |> List.flatten;

    cases_direct =
      List.map (fun term ->
          hashes_of_term ~system term hash_fn key_n
          |> List.map (fun (is,m) ->
              { d_key_indices = is;
                d_message = m })
        ) [mess;sign]
      |> List.flatten }
