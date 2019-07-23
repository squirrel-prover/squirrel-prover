open Term

(** This is [Process.block], but using the types of module [Term] instead of
    module [Theory].
    - binded indices appear in the [binded_indices] field.
    - [ts] contains the variable representing the block timestamp. *)
type block = {
  ts : Term.tvar;
  action : Term.action;
  binded_indices : Term.indices;
  condition : Term.fact;
  updates : (Term.state * Term.term) list;
  output : Term.term }

type process = block list

let subst_block inu tnu blk =
  { ts = app_subst tnu blk.ts;
    action = blk.action;
    binded_indices = List.map (app_subst inu) blk.binded_indices;
    condition = subst_fact inu tnu blk.condition;
    updates = List.map (fun (s,t) -> ivar_subst_state inu s,
                                     subst_term inu tnu t
                       ) blk.updates;
    output = subst_term inu tnu blk.output }

(* let block_ts block =
 *   let open Euf in
 *   List.fold_left (fun acc (_,t) ->
 *       term_ts t @ acc
 *     ) (term_ts block.output) block.updates
 *   |> List.sort_uniq Pervasives.compare *)

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
    [e] of type [euf_case] represents the fact that the message [e.m]
    has been hashed, and the key indices were [e.eindices].
    [e.block] stores the relevant block for future potential use.  *)
type euf_case = { key_indices : Term.indices;
                  message : Term.term;
                  block : block }

(** Type of an euf axiom rule:
    - [hash] stores the hash function name.
    - [key] stores the key considered in this rule.
    - [cases] is the list (seen as a disjunction) of cases, with all relevant
    information.*)
type euf_rule = { hash : fname;
                  key : name;
                  cases : euf_case list }

(** Exception thrown when the axiom syntactic side-conditions do not hold. *)
exception Bad_ssc

(** [mk_rule proc hash_fn key_n] create the euf rule associated to an given
    hash function and key in a process.
    TODO: memoisation *)
let mk_rule proc hash_fn key_n =
  if not @@ euf_key_ssc proc hash_fn key_n then raise Bad_ssc
  else { hash = hash_fn;
         key = key_n;
         cases =
           List.map (fun blk ->
               hashes_of_blk blk hash_fn key_n
               |> List.map (fun (is,m) ->
                   { key_indices = is;
                     message = m;
                     block = blk })
             ) proc
           |> List.flatten }
