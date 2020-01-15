(* Exception thrown when the axiom syntactic side-conditions do not hold. *)
exception Bad_ssc

class check_hash_key hash_fn key_n = object (self)
  inherit Iter.iter_approx_macros as super
  method visit_term t = match t with
    | Term.Fun ((fn,_), [m;Term.Name _]) when fn = hash_fn -> self#visit_term m
    | Term.Name (n,_) when n = key_n -> raise Bad_ssc
    | Term.Var m ->
      (match Vars.var_type m with
      | Sorts.Message-> raise Bad_ssc
      )
    | _ -> super#visit_term t
end

(* Check the key syntactic side-condition:
    The key [key_n] must appear only in key position of the hash [hash_fn]. *)
let euf_key_ssc hash_fn key_n messages =
  let ssc = new check_hash_key hash_fn key_n in
  List.iter ssc#visit_term messages ;
  Action.(iter_descrs
    (fun action_descr ->
       ssc#visit_formula (snd action_descr.condition) ;
       ssc#visit_term (snd action_descr.output) ;
       List.iter (fun (_,t) -> ssc#visit_term t) action_descr.updates))

let hash_key_ssc hash_fn key_n messages =
  try
    euf_key_ssc hash_fn key_n messages;
    true
  with Bad_ssc -> false

let rec h_o_term hh kk acc = function
  | Term.Fun ((fn,_), [m;k]) when fn = hh -> begin match k with
      | Term.Name (key_n',is) ->
        if key_n' = kk then h_o_term hh kk ((is,m) :: acc) m
        else h_o_term hh kk acc m
      | _ -> h_o_term hh kk (h_o_term hh kk acc m) k end

  | Term.Fun (_,l) -> List.fold_left (h_o_term hh kk) acc l
  | Term.Macro ((mn,is),l,a) ->
    if mn = fst Term.in_macro || mn = fst Term.out_macro then acc
    else if Macros.is_defined mn a then
      let acc = List.fold_left (fun acc t -> h_o_term hh kk acc t) acc l in
      Macros.get_definition mn is a
      |> h_o_term hh kk acc
    else raise Bad_ssc
  | Term.Name (_,_) -> acc
  | Term.Var _ -> acc

(** [hashes_of_action_descr action_descr hash_fn key_n] return the pairs of
    indices and messages where a hash using occurs in an action description.
    I.e. we have a pair (is,m) iff hash_fn(m,key_n(is)) occurs in the action
    description output or state updates.
    Remark: we do not need to look in the condition (C.f. axiom P-EUF-MAC). *)
let hashes_of_action_descr action_descr hash_fn key_n =
  List.fold_left (h_o_term hash_fn key_n)
    [] Action.(snd action_descr.output :: (List.map snd action_descr.updates))
  |> List.sort_uniq Pervasives.compare

let hashes_of_term term hash_fn key_n = h_o_term hash_fn key_n [] term

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

let mk_rule ~env ~mess ~sign ~hash_fn ~key_n ~key_is =
  euf_key_ssc hash_fn key_n [mess;sign];
  { hash = hash_fn;
    key = key_n;
    case_schemata =
      Utils.map_of_iter Action.iter_descrs
        (fun action_descr ->
          let env = ref env in
          hashes_of_action_descr action_descr hash_fn key_n
          |> List.map (fun (is,m) ->
            let subst_fresh =
              List.map
                (fun i ->
                   Term.ESubst (Term.Var i,Term.Var
                                  (Vars.make_fresh_from_and_update env i)
                               )
                )
                (List.filter
                   (fun x -> not (List.mem x is))
                   action_descr.Action.indices)
            in
            let subst_is =
              List.map2
                (fun i j -> Term.ESubst (Term.Var i, Term.Var j))
                is key_is
            in
            let subst = subst_fresh@subst_is in
            let new_action_descr = Action.subst_descr subst action_descr in
            { message = Term.subst subst m ;
              action_descr = new_action_descr;
              env = !env })
        )
      |> List.flatten;

    cases_direct =
      List.map (fun term ->
          hashes_of_term term hash_fn key_n
          |> List.map (fun (is,m) ->
              { d_key_indices = is;
                d_message = m })
        ) [mess;sign]
      |> List.flatten }
