(** Old utilities for CCA-based tactics.
    will disappear soon, only left here for enc-kp *)

(* TODO: better error message, see [OldEuf] *)
exception Bad_ssc

class deprecated_check_symenc_key ~cntxt enc_fn dec_fn key_n = object (self)
  inherit Iter.deprecated_iter_approx_macros ~exact:false ~cntxt as super
  method visit_message t = match t with
    | Term.Fun (fn, _, [Tuple [m;r;k]]) when fn = enc_fn && Term.diff_names k ->
      self#visit_message m; self#visit_message r
    | Term.Fun (fn, _, [Tuple [m;k]]) when fn = dec_fn && Term.diff_names k ->
      self#visit_message m
    | Term.Name (ns,_) when ns.s_symb = key_n -> raise Bad_ssc
    | Term.Var m ->
      let ty = Vars.ty m in
      if ty <> Type.tindex && ty <> Type.ttimestamp then
        raise Bad_ssc

    | _ -> super#visit_message t
end

let deprecated_symenc_key_ssc ?(messages=[]) ?(elems=[]) ~cntxt enc_fn dec_fn key_n =
  let ssc = new deprecated_check_symenc_key ~cntxt enc_fn dec_fn key_n in
  List.iter ssc#visit_message messages ;
  List.iter ssc#visit_message elems ;
  SystemExpr.iter_descrs cntxt.table cntxt.system
    (fun action_descr ->
       ssc#visit_message (snd action_descr.condition) ;
       ssc#visit_message (snd action_descr.output) ;
       List.iter (fun (_,_,t) -> ssc#visit_message t) action_descr.updates)


(* Iterator to check that the given randoms are only used in random seed
   position for encryption. *)
class deprecated_check_rand ~cntxt enc_fn randoms = object (self)
  inherit Iter.deprecated_iter_approx_macros ~exact:false ~cntxt as super
  method visit_message t = match t with
    | Term.Fun (fn, _, [Tuple [m1;Term.Name _; m2]]) when fn = enc_fn ->
      self#visit_message m1; self#visit_message m2

    | Term.Fun (fn, _, [Tuple [_; _; _]]) when fn = enc_fn ->
      raise Bad_ssc

    | Term.Name (ns,_) when List.mem ns.s_symb randoms ->
      Tactics.soft_failure (Tactics.SEncRandomNotFresh)

    | Term.Var m ->
      let ty = Vars.ty m in
      if ty <> Type.tindex && ty <> Type.ttimestamp then
        Tactics.soft_failure
          (Tactics.Failure "No universal quantification over \
                            messages allowed")
    | _ -> super#visit_message t
end

(* Check that the given randoms are only used in random seed position for
   encryption. *)
let deprecated_random_ssc
    ?(messages=[]) ?(elems=[])
    ~cntxt enc_fn randoms =
  let ssc = new deprecated_check_rand ~cntxt enc_fn randoms in
  List.iter ssc#visit_message messages;
  List.iter ssc#visit_message elems;
  SystemExpr.iter_descrs cntxt.table cntxt.system
    (fun action_descr ->
       ssc#visit_message (snd action_descr.condition) ;
       ssc#visit_message (snd action_descr.output) ;
       List.iter (fun (_,_,t) -> ssc#visit_message t) action_descr.updates)


  (* Given cases produced by an OldEuf.mk_rule for some symmetric encryption
     scheme, check that all occurences of the encryption use a dedicated
     randomness.
     It checks that:
      - a randomness is only used inside a randomness position
      - there does not exists two messages from different place with the
     same randomness
      - if inside an action A[I], the encryption enc(m,r,sk) is produced,
       the index variables appearing in both m and I should also appear in r.

     This could be refined into a tactic where we ask to prove that encryptions
     that use the same randomness are done on the same plaintext. This is why we
     based ourselves on messages produced by OldEuf.mk_rule, which should simplify
     such extension if need. *)
let deprecated_check_encryption_randomness
    ~cntxt case_schemata cases_direct enc_fn messages elems =
  let encryptions : (Term.term * Vars.var list) list =
    List.map (fun case ->
        case.OldEuf.message,
        Action.get_args_v case.OldEuf.action
      ) case_schemata
    @
    List.map (fun case -> case.OldEuf.d_message, []) cases_direct
  in
  let encryptions = List.sort_uniq Stdlib.compare encryptions in

  let randoms = 
    List.map (function
        | Term.Fun (_, _, [Tuple [_; Name (r,_); _]]), _-> r.s_symb
        | _ ->  Tactics.soft_failure Tactics.SEncNoRandom
      ) encryptions
  in
  deprecated_random_ssc ~elems ~messages ~cntxt enc_fn randoms;

  (* TODO: AST: this test is insufficient. Crypto tactic rework ? *)
  (* we check that encrypted messages based on indices, do not depend on free
     indices instantiated by the action w.r.t the indices of the random. *)
  if List.exists (function
      | Term.Fun (_, _, [Tuple [m; Name (_n,n_args); _]]), 
        (actidx : Vars.var list) ->
        let vars = Term.get_vars m in
        let n_args_vars =
          (* keep only term in [n_args] which are top-level variables *)
          List.filter_map (function
              | Term.Var v -> Some v
              | _ -> None       (* could allow [Tuple \[Var _; ...; Var _\]] *)
            ) n_args
        in

        List.exists (fun v ->
            (* TODO: the test below is insufficient, and needs to check 
               that this holds not only for [actidx], but for all bound 
               variables (see issue #179). *)
            (List.mem v actidx) && not (List.mem v n_args_vars)
            (* we fail if there exists a variable appearing in the message,
               which is an indice instantiated by the action description,
               and it does not appear in the random. *)
          ) vars
      | _ -> assert false
    ) encryptions
  then
    Tactics.soft_failure Tactics.SEncSharedRandom;

  (* we check that no encryption is shared between multiple encryptions *)
  let enc_classes = Utils.classes (fun m1 m2 ->
      match m1, m2 with
      | (Term.Fun (_, _, [Tuple [m1; Name (r,_) ; k1]]),_),
        (Term.Fun (_, _, [Tuple [m2; Name (r2,_); k2]]),_) ->
        r.s_symb = r2.s_symb &&
        (m1 <> m2 || k1 <> k2)
      (* the patterns should match, if they match inside the declaration
         of randoms *)
      | _ -> assert false
    ) encryptions in

  if List.exists (fun l -> List.length l > 1) enc_classes then
    Tactics.soft_failure Tactics.SEncSharedRandom


let deprecated_symenc_rnd_ssc ~cntxt env head_fn ~key ~key_is elems =
  let rule =
    OldEuf.mk_rule
      ~fun_wrap_key:None
      ~elems ~drop_head:false
      ~allow_functions:(fun _ -> false)
      ~cntxt ~env ~mess:Term.empty ~sign:Term.empty
      ~head_fn ~key_n:key.Term.s_symb ~key_is
  in
  deprecated_check_encryption_randomness ~cntxt
    rule.OldEuf.case_schemata rule.OldEuf.cases_direct head_fn [] elems
