open Term
open Process

(* type process = descr list *)

let subst_descr nu blk =
  { action = blk.action;
    indices = List.map (subst_index nu) blk.indices;
    condition = subst_fact nu blk.condition;
    updates = List.map (fun (s, t) -> subst_state nu s,
                                      subst_term nu t
                       ) blk.updates;
    output = subst_term nu blk.output }

(* Exception thrown when the axiom syntactic side-conditions do not hold. *)
exception Bad_ssc

(* Check the key syntactic side-condition:
    The key [key_n] must appear only in key position of the hash [hash_fn]. *)
let euf_key_ssc hash_fn key_n =
  let checked_macros = ref [] in

  let rec ssc_blk blk =
    ssc_fact blk.condition;
    ssc_term blk.output;
    List.iter (fun (_,t) -> ssc_term t) blk.updates

  and ssc_fact = function
    | And (l, r) -> ssc_fact l; ssc_fact r
    | Or (l, r) -> ssc_fact l; ssc_fact r
    | Impl (l, r) -> ssc_fact l; ssc_fact r
    | Not f -> ssc_fact f
    | True | False -> ()
    | Atom (_, t, t') -> ssc_term t; ssc_term t'

  and ssc_term = function
    | Fun ((fn, _), [m; k]) when fn = hash_fn ->
      begin match k with
        | Name _ -> ssc_term m
        | _ -> ssc_term m; ssc_term k
      end

    | Fun (_, l) -> List.iter ssc_term l
    | Macro ((mn, is), _) -> ssc_macro mn is
    | State _ -> ()
    | Name (n, _) -> if n = key_n then raise Bad_ssc
    | MVar m -> raise Bad_ssc

  and ssc_macro mn is =
    if List.mem mn !checked_macros || Term.is_built_in mn then ()
    else begin
      checked_macros := mn :: !checked_macros;
      let rec dummy_action k =
        if k = 0 then [] else
          { Action.par_choice = 0,[] ; sum_choice = 0,[] }
          :: dummy_action (k-1)
      in
      let dummy_action = dummy_action (Term.macro_domain mn) in
      ssc_term (Term.macro_declaration mn dummy_action is) end in

  Process.iter_fresh_csa ssc_blk


let rec h_o_term hh kk acc = function
  | Fun ((fn,_), [m;k]) when fn = hh -> begin match k with
      | Name (key_n',is) ->
        if key_n' = kk then h_o_term hh kk ((is,m) :: acc) m
        else h_o_term hh kk acc m
      | _ -> h_o_term hh kk (h_o_term hh kk acc m) k end

  | Fun (_,l) -> List.fold_left (h_o_term hh kk) acc l
  | Macro ((mn,is),a) ->
    if Term.is_built_in mn then acc
    else begin match a with
      | Term.TName a when List.length a = Term.macro_domain mn ->
          Term.macro_declaration mn a is
          |> h_o_term hh kk acc
      | _ -> raise Bad_ssc
    end
  | State _ -> acc
  | Name (n,_) -> acc
  | MVar m -> acc

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

type euf_schema = { key_indices : Action.index list;
                    message : Term.term;
                    blk_descr : descr }

let pp_euf_schema ppf case =
  Fmt.pf ppf "@[<v>@[<hv 2>*action:@ @[<hov>%a@]@]@;\
              @[<hv 2>*key indices:@ @[<hov>%a@]@]@;\
              @[<hv 2>*message:@ @[<hov>%a@]@]"
    Action.pp_action case.blk_descr.action
    Action.Index.pp_list case.key_indices
    Term.pp_term case.message

(** Type of a direct euf axiom case.
    [e] of type [euf_case] represents the fact that the message [e.m]
    has been hashed, and the key indices were [e.eindices]. *)
type euf_direct = { d_key_indices : Action.index list;
                    d_message : Term.term }


let pp_euf_direct ppf case =
  Fmt.pf ppf "@[<v>@[<hv 2>*key indices:@ @[<hov>%a@]@]@;\
              @[<hv 2>*message:@ @[<hov>%a@]@]"
    Action.Index.pp_list case.d_key_indices
    Term.pp_term case.d_message

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

let mk_rule mess sign hash_fn key_n =
  euf_key_ssc hash_fn key_n;
  { hash = hash_fn;
    key = key_n;

    case_schemata =
      Utils.map_of_iter Process.iter_fresh_csa
        (fun blk ->
           hashes_of_blk blk hash_fn key_n
           |> List.map (fun (is, m) ->
               { key_indices = is;
                 message = m;
                 blk_descr = blk })
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
