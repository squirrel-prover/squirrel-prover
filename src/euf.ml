open Term
open Bformula
open Process

(* type process = descr list *)

(* TODO why is it different from [Process.subst_descr] ? *)
let subst_descr nu blk =
  { action = blk.action;
    indices = List.map (subst_index nu) blk.indices;
    condition = subst_fact nu blk.condition;
    updates = List.map (fun (s, t) -> subst_macro nu s,
                                      subst_term nu t
                       ) blk.updates;
    output = subst_term nu blk.output }

(* Exception thrown when the axiom syntactic side-conditions do not hold. *)
exception Bad_ssc

class check_hash_key hash_fn key_n = object (self)
  inherit Iter.iter_approx_macros as super
  method visit_term t = match t with
    | Fun ((fn,_), [m;Name _]) when fn = hash_fn -> self#visit_term m
    | Name (n,_) when n = key_n -> raise Bad_ssc
    | MVar m -> raise Bad_ssc
    | _ -> super#visit_term t
end

(* Check the key syntactic side-condition:
    The key [key_n] must appear only in key position of the hash [hash_fn]. *)
let euf_key_ssc hash_fn key_n messages =
  let ssc = new check_hash_key hash_fn key_n in
  List.iter ssc#visit_term messages ;
  Process.iter_csa
    (fun blk ->
       ssc#visit_fact blk.condition ;
       ssc#visit_term blk.output ;
       List.iter (fun (_,t) -> ssc#visit_term t) blk.updates)

let rec h_o_term hh kk acc = function
  | Fun ((fn,_), [m;k]) when fn = hh -> begin match k with
      | Name (key_n',is) ->
        if key_n' = kk then h_o_term hh kk ((is,m) :: acc) m
        else h_o_term hh kk acc m
      | _ -> h_o_term hh kk (h_o_term hh kk acc m) k end

  | Fun (_,l) -> List.fold_left (h_o_term hh kk) acc l
  | Macro ((mn,is),l,a) ->
    if mn = fst Term.in_macro || mn = fst Term.out_macro then acc
    else if Term.Macro.is_defined mn a then
      let acc = List.fold_left (fun acc t -> h_o_term hh kk acc t) acc l in
      Term.Macro.get_definition mn is a
      |> h_o_term hh kk acc
    else raise Bad_ssc
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
                    blk_descr : descr;
                    env : Vars.env }

let pp_euf_schema ppf case =
  Fmt.pf ppf "@[<v>@[<hv 2>*action:@ @[<hov>%a@]@]@;\
              @[<hv 2>*key indices:@ @[<hov>%a@]@]@;\
              @[<hv 2>*message:@ @[<hov>%a@]@]"
    Action.pp_action case.blk_descr.action
    Vars.pp_list case.key_indices
    Term.pp_term case.message

(** Type of a direct euf axiom case.
    [e] of type [euf_case] represents the fact that the message [e.m]
    has been hashed, and the key indices were [e.eindices]. *)
type euf_direct = { d_key_indices : Action.index list;
                    d_message : Term.term }


let pp_euf_direct ppf case =
  Fmt.pf ppf "@[<v>@[<hv 2>*key indices:@ @[<hov>%a@]@]@;\
              @[<hv 2>*message:@ @[<hov>%a@]@]"
    Vars.pp_list case.d_key_indices
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

let mk_rule env_init mess sign hash_fn key_n =
  euf_key_ssc hash_fn key_n [mess;sign];
  { hash = hash_fn;
    key = key_n;

    case_schemata =
      Utils.map_of_iter Process.iter_csa_block
        (fun blk ->
          let env = ref env_init in
          let new_block = Process.fresh_instance env blk in
          hashes_of_blk new_block hash_fn key_n
          |> List.map (fun (is, m) ->
            { key_indices = is;
             message = m;
             blk_descr = new_block;
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
