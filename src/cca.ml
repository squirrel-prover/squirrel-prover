open Term

class check_symenc_key ~cntxt enc_fn dec_fn key_n = object (self)
  inherit Iter.iter_approx_macros ~exact:false ~full:true ~cntxt as super
  method visit_message t = match t with
    | Term.Fun ((fn,_), [m;r; Term.Name _]) when fn = enc_fn ->
      self#visit_message m; self#visit_message r
    | Term.Fun ((fn,_), [m; Term.Name _]) when fn = dec_fn ->
      self#visit_message m
    | Term.Fun ((fn,_), [m;r; Diff(Term.Name _, Term.Name _)]) when fn = enc_fn ->
      self#visit_message m; self#visit_message r
    | Term.Fun ((fn,_), [m;  Diff(Term.Name _, Term.Name _)]) when fn = dec_fn ->
      self#visit_message m
    | Term.Name (n,_) when n = key_n -> raise Euf.Bad_ssc
    | Term.Var m -> raise Euf.Bad_ssc
    | _ -> super#visit_message t
end

let symenc_key_ssc ?(messages=[]) ?(elems=[]) ~cntxt enc_fn dec_fn key_n =
  let ssc = new check_symenc_key ~cntxt enc_fn dec_fn key_n in
  List.iter ssc#visit_message messages ;
  List.iter ssc#visit_term elems ;
  SystemExpr.(iter_descrs cntxt.table cntxt.system
    (fun action_descr ->
       ssc#visit_formula (snd action_descr.condition) ;
       ssc#visit_message (snd action_descr.output) ;
       List.iter (fun (_,t) -> ssc#visit_message t) action_descr.updates))


(* Iterator to check that the given randoms are only used in random seed
   position for encryption. *)
class check_rand ~allow_vars ~cntxt enc_fn randoms = object (self)
  inherit Iter.iter_approx_macros ~exact:false ~full:true ~cntxt as super
  method visit_message t = match t with
    | Term.Fun ((fn,_), [m1;Term.Name _; m2]) when fn = enc_fn ->
      self#visit_message m1; self#visit_message m2
    | Term.Fun ((fn,_), [m1; _; m2]) when fn = enc_fn ->
      raise Euf.Bad_ssc
    | Term.Name (n,_) when List.mem n randoms ->
      Tactics.soft_failure (Tactics.SEncRandomNotFresh)
    | Term.Var m -> if not(allow_vars) then
        Tactics.soft_failure (Tactics.Failure "No universal quantification over \
                                               messages allowed")
    | _ -> super#visit_message t
end

(* Check that the given randoms are only used in random seed position for
   encryption. *)
let random_ssc
    ?(allow_vars=false) ?(messages=[]) ?(elems=[]) 
    ~cntxt enc_fn randoms =
  let ssc = new check_rand ~allow_vars ~cntxt enc_fn randoms in
  List.iter ssc#visit_message messages;
  List.iter ssc#visit_term elems;
  SystemExpr.(iter_descrs cntxt.table cntxt.system
    (fun action_descr ->
       ssc#visit_formula (snd action_descr.condition) ;
       ssc#visit_message (snd action_descr.output) ;
       List.iter (fun (_,t) -> ssc#visit_message t) action_descr.updates))


  (* Given cases produced by an Euf.mk_rule for some symmetric encryption
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
     based ourselves on messages produced by Euf.mk_rule, which should simplify
     such extension if need. *)
let check_encryption_randomness 
    ~cntxt case_schemata cases_direct enc_fn messages elems =
  let encryptions : (Term.message * Vars.index list) list = 
    List.map (fun case -> 
        case.Euf.message,
        case.Euf.action_descr.indices
      ) case_schemata
    @
    List.map (fun case -> case.Euf.d_message, []) cases_direct
  in
  let encryptions = List.sort_uniq Stdlib.compare encryptions in

  let randoms = List.map (function
      | Fun ((_, _), [_; Name (r, is); _]), _-> r
      | _ ->  Tactics.soft_failure (Tactics.SEncNoRandom))
      encryptions
  in
  random_ssc ~elems ~messages ~cntxt enc_fn randoms;

  (* we check that encrypted messages based on indices, do not depend on free
     indices instantiated by the action w.r.t the indices of the random. *)
  if List.exists (function
      | (Fun ((_, _), [m; Name (_, is); _]), (actidx:Vars.index list)) ->
        let vars = Term.get_vars m in
        List.exists (function
              Vars.EVar v ->
              (match Vars.sort v with
               |Sorts.Index -> (List.mem v actidx) && not (List.mem v is)
               (* we fail if there exists an indice appearing in the message,
                  which is an indice instantiated by the action description,
                  and it does not appear in the random. *)
               | _ -> false)) vars
      | _ -> assert false) encryptions then    
    Tactics.soft_failure (Tactics.SEncSharedRandom);

  (* we check that no encryption is shared between multiple encryptions *)
  let enc_classes = Utils.classes (fun m1 m2 ->
      match m1, m2 with
      | (Fun ((_, _), [_; Name (r, is); _]),_), 
        (Fun ((_, _), [_; Name (r2,is2); _]),_) -> (r = r2)
      (* the patterns should match, if they match inside the declaration
         of randoms *)
      | _ -> assert false
    ) encryptions in

  if List.exists (fun l -> List.length l > 1) enc_classes then
    Tactics.soft_failure (Tactics.SEncSharedRandom)


let symenc_rnd_ssc ~cntxt env head_fn key_n key_is elems =
  let rule =
    Euf.mk_rule ~elems ~drop_head:false ~allow_functions:(fun x -> false)
      ~cntxt ~env ~mess:Term.empty ~sign:Term.empty
      ~head_fn ~key_n ~key_is
  in
  check_encryption_randomness ~cntxt
    rule.Euf.case_schemata rule.Euf.cases_direct head_fn [] elems
