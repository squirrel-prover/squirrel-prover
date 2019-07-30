open Term
open Process

type process = descr list

let subst_descr inu tnu blk =
  { action = blk.action;
    indices = List.map (Action.app_subst inu) blk.indices;
    condition = subst_fact inu tnu blk.condition;
    updates = List.map (fun (s,t) -> ivar_subst_state inu s,
                                     subst_term inu tnu t
                       ) blk.updates;
    output = subst_term inu tnu blk.output }

(* let descr_ts descr =
 *   let open Euf in
 *   List.fold_left (fun acc (_,t) ->
 *       term_ts t @ acc
 *     ) (term_ts descr.output) descr.updates
 *   |> List.sort_uniq Pervasives.compare *)

(** Check the key syntactic side-condition:
    The key [key_n] must appear only in key position of the hash [hash_fn]. *)
let euf_key_ssc proc hash_fn key_n =
  let checked_macros = ref [] in

  let rec ssc_blk blk =
    ssc_fact blk.condition
    && ssc_term blk.output
    && List.for_all (fun (_,t) -> ssc_term t) blk.updates

  and ssc_fact = function
    | And (l,r) -> ssc_fact l && ssc_fact r
    | Or (l,r) -> ssc_fact l && ssc_fact r
    | Impl (l,r) -> ssc_fact l && ssc_fact r
    | Not f -> ssc_fact f
    | True | False -> true
    | Atom (_,t,t') -> ssc_term t && ssc_term t'

  and ssc_term = function
    | Fun ((fn,_), [m;k]) when fn = hash_fn -> begin match k with
        | Name _ -> ssc_term m
        | _ -> ssc_term m && ssc_term k end

    | Fun (_,l) -> List.for_all ssc_term l
    (* | Output _ | Input _ *)
    | Macro ((mn,is),_) -> ssc_macro mn is
    | State _ -> true
    | Name (n,_) -> n <> key_n

  and ssc_macro mn is =
    if List.mem mn !checked_macros || Term.is_built_in mn then true
    else begin
      checked_macros := mn :: !checked_macros;
      let a_dummy = Action.mk_action [] in
      ssc_term (Term.macro_declaration mn (TName a_dummy) is) end in

  List.for_all ssc_blk  proc


let rec h_o_term hh kk acc = function
  | Fun ((fn,_), [m;k]) when fn = hh -> begin match k with
      | Name (key_n',is) ->
        if key_n' = kk then h_o_term hh kk ((is,m) :: acc) m
        else h_o_term hh kk acc m
      | _ -> h_o_term hh kk (h_o_term hh kk acc m) k end

  | Fun (_,l) -> List.fold_left (h_o_term hh kk) acc l
  | Macro ((mn,is),a) ->
    if Term.is_built_in mn then acc
    else Term.macro_declaration mn a is
         |> h_o_term hh kk acc
  | State _ -> acc
  | Name (n,_) -> acc

(** [hashes_of_blk blk hash_fn key_n] return the pairs of indices and messages
    where a hash using occurs in a block description. I.e. we have a pair
    (is,m) iff hash_fn(m,key_n(is)) occurs in the block description output or
    state updates.
    Remark: we do not need to look in the condition (C.f. axiom P-EUF-MAC). *)
let hashes_of_blk blk hash_fn key_n =
  List.fold_left (h_o_term hash_fn key_n)
    [] (blk.output :: (List.map snd blk.updates))
  |> List.sort_uniq Pervasives.compare

let hashes_of_term term hash_fn key_n = h_o_term hash_fn key_n [] term



(** Type of an euf axiom case schema.
    [e] of type [euf_schema] represents the fact that the message [e.m]
    has been hashed, and the key indices were [e.eindices].
    [e.blk_block] stores the relevant block description for future use.  *)
type euf_schema = { key_indices : Action.indices;
                    message : Term.term;
                    blk_descr : descr }


let pp_euf_schema ppf case =
  Fmt.pf ppf "@[<v>@[<hv 2>*action:@ @[<hov>%a@]@]@;\
              @[<hv 2>*key indices:@ @[<hov>%a@]@]@;\
              @[<hv 2>*message:@ @[<hov>%a@]@]"
    Action.pp_action case.blk_descr.action
    Action.pp_indices case.key_indices
    Term.pp_term case.message

(** Type of a direct euf axiom case.
    [e] of type [euf_case] represents the fact that the message [e.m]
    has been hashed, and the key indices were [e.eindices]. *)
type euf_direct = { d_key_indices : Action.indices;
                    d_message : Term.term }


let pp_euf_direct ppf case =
  Fmt.pf ppf "@[<v>@[<hv 2>*key indices:@ @[<hov>%a@]@]@;\
              @[<hv 2>*message:@ @[<hov>%a@]@]"
    Action.pp_indices case.d_key_indices
    Term.pp_term case.d_message


(** Type of an euf axiom rule:
    - [hash] stores the hash function name.
    - [key] stores the key considered in this rule.
    - [case_schemata] is the list (seen as a disjunction) of case schemata.
    - [cases_direct] is the list (seen as a disjunction) of direct cases. *)
type euf_rule = { hash : fname;
                  key : name;
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

(** Exception thrown when the axiom syntactic side-conditions do not hold. *)
exception Bad_ssc

(** [mk_rule proc mess sign hash_fn key_n] create the euf rule associated to
    an given hash function, key, message and signature in a process.
    TODO: memoisation *)
let mk_rule proc mess sign hash_fn key_n =
  if not @@ euf_key_ssc proc hash_fn key_n then raise Bad_ssc
  else
    { hash = hash_fn;
      key = key_n;

      case_schemata =
        List.map (fun blk ->
            hashes_of_blk blk hash_fn key_n
            |> List.map (fun (is,m) ->
                { key_indices = is;
                  message = m;
                  blk_descr = blk })
          ) proc
        |> List.flatten;

      cases_direct =
        List.map (fun term ->
            hashes_of_term term hash_fn key_n
            |> List.map (fun (is,m) ->
                { d_key_indices = is;
                  d_message = m })
          ) [mess;sign]
        |> List.flatten }
