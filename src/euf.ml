open Term

(** This is [Process.block], but using the types of module [Term] instead of
    module [Theory]. Binded indices appear in the [binded_indices] field. *)
type block = {
  action : action;
  binded_indices : indices;
  condition : fact;
  updates : (state * term) list;
  output : term }

type process = block list

(** Check the key syntactic side-condition:
    The key [key_n] must appear only in key position of the hash [hash_fn]. *)
let euf_key_ssc proc hash_fn key_n =
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
    | Output _ | Input _ | State _ -> true
    | Name (n,_) -> n <> key_n in

  List.for_all ssc_blk  proc


(** [hashes_of_blk blk hash_fn key_n] return the pairs of indices and messages
    where a hash using occurs in a block. I.e. we have a pair (is,m) iff
    hash_fn(m,key_n(is)) occurs in the block output or state updates.
    Remark: we do not need to look in the condition (C.f. axiom P-EUF-MAC). *)
let hashes_of_blk blk hash_fn key_n =
  let rec h_o_term acc = function
    | Fun ((fn,_), [m;k]) when fn = hash_fn -> begin match k with
        | Name (key_n',is) ->
          if key_n' = key_n then h_o_term ((is,m) :: acc) m
          else h_o_term acc m
        | _ -> h_o_term (h_o_term acc m) k end

    | Fun (_,l) -> List.fold_left h_o_term acc l
    | Output _ | Input _ | State _ -> acc
    | Name (n,_) -> acc in

  List.fold_left h_o_term [] (blk.output :: (List.map snd blk.updates))
  |> List.sort_uniq Pervasives.compare


(** Type of an euf axiom case.
   [e] of type [euf_case] represents the fact that, at timestamp
   [e.action(e.eindices)], the message [e.m] has been hashed.
   [e.block] stores the relevant block for future potential use.  *)
type euf_case = { eindices : indices;
                  action : action;
                  message : term;
                  block : block }

(** Type of an euf axiom rule:
    - [hash] stores the hash function name.
    - [key] stores the key considered in this rule.
    - [cases] is the list (seen as a disjunction) of cases, with all relevant
    information.*)
type euf_rule = { hash : fname;
                  key : name;
                  cases : euf_case list }

exception Bad_ssc

(** [mk_rule proc hash_fn key_n] create the euf rule associated to an given
    hash function and key in a process. *)
let mk_rule proc hash_fn key_n =
  if not @@ euf_key_ssc proc hash_fn key_n then raise Bad_ssc;
  { hash = hash_fn; key = key_n;
    cases =
      List.map (fun blk ->
          hashes_of_blk blk hash_fn key_n
          |> List.map (fun (is,m) ->
              { eindices = is;
                action = blk.action;
                message = m;
                block = blk })
        ) proc
      |> List.flatten }
