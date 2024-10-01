(** Utilities to check side-conditions on the injective use of encryption
    randomness for crypto rules (ind-cca, int-ctxt) *)

open Squirrelcore
open Term

module LT = LowTactics

module O = Occurrences
module Name = O.Name
type name = Name.t



(*------------------------------------------------------------------*)
(** {2 Instantiation of the Occurrences module } *)

(** Exported (see `.mli`) *)
type enc_content =
  | BadName of name
  | Ciphertext of term
  | NoCipher

(** Exported (see `.mli`) *)
type enc_data =
  | DataCiphertext of {msg:term; rand:name; key:name; keycoll:name}
  | NoData

(** Exported (see `.mli`) *)
module EncryptionOC : O.OccurrenceContent
  with type content = enc_content
   and type data = enc_data =
struct
  type content = enc_content
  type data = enc_data

  let collision_formula ~(negate : bool)
      ~(content : content) ~(collision : content) ~(data : data)
    : Term.term
    =
    match content, collision, data with
    | BadName n, BadName ncoll, NoData ->
      (* sanity check: this should only happen
         if they have the same symbol *)
      assert (n.symb = ncoll.symb);
      if not negate then
        Term.mk_eqs ~simpl:true ~simpl_tuples:true ncoll.args n.args
      else
        Term.mk_neqs ~simpl:false ~simpl_tuples:true ncoll.args n.args

    | Ciphertext c, NoCipher, DataCiphertext d ->
      (* in that case, we will not use the generated formula -- we only want
         to gather all ciphertexts. We still generate a term containing
         c and the key, which is used to remove duplicates. *)
      (* sanity check: the key and keycoll in d have the same symbol *)
      assert (d.key.symb = d.keycoll.symb);
      (* sanity check: the msg, random, and key in d match those in c *)
      let _ =
        match c with
        | App (Fun _, [Tuple [m; Name _ as r; Name _ as k]])
          when Term.equal m d.msg &&
               Term.equal r (Name.to_term d.rand) &&
               Term.equal k (Name.to_term d.key) -> ()
        | _ -> assert false
      in

      let t = mk_tuple [c; Name.to_term d.keycoll] in
      mk_eq ~simpl:false t t

    | _ ->
      (* sanity check: we should never record a collision between two things
         with a different constructor *)
      assert false

  let subst_content sigma x =
    match x with
    | BadName n -> BadName (Name.subst sigma n)
    | Ciphertext c -> Ciphertext (Term.subst sigma c)
    | NoCipher -> NoCipher

  let subst_data sigma d =
    match d with
    | DataCiphertext d ->
      DataCiphertext
        {msg = subst sigma d.msg;
         rand = Name.subst sigma d.rand;
         key = Name.subst sigma d.key;
         keycoll = Name.subst sigma d.keycoll} (* should do nothing *)
    | _ -> d

  let pp_content ppe fmt x =
    match x with
    | BadName n ->
      Fmt.pf fmt "%a" (Name.pp ppe) n
    | Ciphertext c ->
      Fmt.pf fmt "%a" (Term._pp ppe) c
    | NoCipher -> ()

  let pp_data ppe fmt d : unit =
    match d with
    | DataCiphertext d -> (* do we want to print more info? we'll see *)
      Fmt.pf fmt "(encrypted with key %a)" (Name.pp ppe) d.keycoll
    | NoData -> ()
end


(** Exported (see `.mli`) *)
module EncryptionOS = O.MakeSearch (EncryptionOC)
module EncryptionOF = O.MakeFormulas (EncryptionOS.EO)

(* shortcuts *)
module EOC = EncryptionOC
module EOS = EncryptionOS



(** Exported (see `.mli`) *)
type rand_content = name
type rand_data = 
  { cipher:enc_content; 
    cipherdata:enc_data; 
    plain: term option; 
    key: name option }


(** Exported (see `.mli`) *)
module RandomnessOC : O.OccurrenceContent
  with type content = rand_content
   and type data = rand_data =
struct
  type content = rand_content
  type data = rand_data

  let collision_formula ~(negate : bool)
      ~(content : content) ~(collision : content) ~(data : data)
    : Term.term
    =
    let rr = collision in
    let rr' = content in

    (* sanity check: the content and collision values have the same symbol *)
    assert (rr'.symb = rr.symb);

    (* retrieve [cc] and the associated data from the occ in data *)
    let kk, k, mm =
      match data.cipher, data.cipherdata with 
      | Ciphertext _, DataCiphertext ccdata -> 
        (* sanity check: rr is in both collision and ccdata *)
        assert (ccdata.rand = rr);
        ccdata.key, ccdata.keycoll, ccdata.msg
      | _ -> assert false; (* sanity check: we cannot have a BadName here *)
    in

    (* sanity check: kk and k have the same symbol *)
    assert (kk.symb = k.symb);

    (* kk = k *)
    let phi_k = mk_eqs ~simpl:true ~simpl_tuples:true kk.args k.args in

    (* rr' = rr *)
    let phi_r = mk_eqs ~simpl:true ~simpl_tuples:true rr'.args rr.args in

    (* kk' <> kk \/ mm' <> mm, if needed (true otherwise) *)
    (* or the negation of that formula, depending on the negate flag *)
    let phi_mk =
      match data.plain, data.key, negate with
      | Some mm', Some kk', false ->
        mk_or 
          (mk_neqs ~simpl:true ~simpl_tuples:true kk'.args kk.args)
          (mk_neq ~simpl:true mm' mm)
      | Some mm', Some kk', true ->
        mk_and
          (mk_eqs ~simpl:true ~simpl_tuples:true kk'.args kk.args)
          (mk_eq ~simpl:true mm' mm)
      | None, None, false -> mk_true
      | None, None, true -> mk_false
      | _ -> assert false
    in

    (* complete formula *)        
    if not negate then
      (* kk = k /\ rr' = rr /\ (kk' <> kk \/ mm' <> mm) *)
      mk_ands [phi_k; phi_r; phi_mk]
    else 
      (* kk' = k => rr' = rr => kk' = kk /\ mm' = mm *)
      mk_impls [phi_r; phi_k] phi_mk

  let subst_content sigma x = Name.subst sigma x

  let subst_data sigma d =
    { cipher = EOC.subst_content sigma d.cipher;
      cipherdata = EOC.subst_data sigma d.cipherdata;
      plain = Option.map (Term.subst sigma) d.plain;
      key = Option.map (Name.subst sigma) d.key; }

  let pp_content ppe fmt x = 
    Fmt.pf fmt "%a" (Name.pp ppe) x

  let pp_data _ fmt d : unit =
    (* do we want to print more info? we'll see *)
    match d.cipher with 
    | Ciphertext c ->
      Fmt.pf fmt "(found in ciphertext %a)" Term.pp c
    | _ -> assert false;
end


(** Exported (see `.mli`) *)
module RandomnessOS = O.MakeSearch (RandomnessOC)
module RandomnessOF = O.MakeFormulas (RandomnessOS.EO)    

(* shortcuts *)
module ROC = RandomnessOC
module ROS = RandomnessOS
module ROF = RandomnessOF


(** Exported (see `.mli`) *)
let mk_randomness_occ
    ~(content : ROC.content)
    ~(vars : Vars.vars) ~(cond : terms) ~(typ : O.occ_type)
    ~(sub : term)
    ~(ciphertext:EOS.EO.ext_occ)
    ~(plain: term option)
    ~(key: name option)
  =
  (* we could maybe add sanity checks here *)
  (* maybe instead of in ROC.collision_formula? *)

  (* TODO would it make sense to also add the time formula for the ciphertext
     occ to the condition? *)
  let collision =
    match ciphertext.eo_occ.so_ad with 
    | DataCiphertext d -> d.rand
    | _ -> assert false
  in
  ROS.EO.SO.mk_simple_occ
    ~content
    ~collision
    ~data:{cipher = ciphertext.eo_occ.so_cnt; (* extract the ciphertext *)
           cipherdata = ciphertext.eo_occ.so_ad; (* extract the cipher data *)
           plain = plain;
           key = key; }
    ~vars:(vars @ ciphertext.eo_occ.so_vars) (* add the ciphertext's vars, so
                                                they are quantified *)
    ~cond:(cond @ ciphertext.eo_occ.so_cond) (* add the ciphertext's cond, which
                                                must hold for the occ to be 
                                                relevant *)
    ~typ
    ~sub
    ~show:Show



(*------------------------------------------------------------------*)
(* Look for occurrences using the Occurrences module *)

(** Exported (see `.mli`) *)
type dec_allowed = Allowed | NotAllowed | NotAbove of name

(** Exported (see `.mli`) *)
let is_dec_allowed (da:dec_allowed) (ts:Term.terms) : bool =
  match da with
  | Allowed -> true
  | NotAllowed -> false
  | NotAbove n -> List.for_all (fun t -> not (Name.has_name n t)) ts


(** Exported (see `.mli`) *)
let get_bad_randoms
    (env : Env.t)
    ~(k : name)
    ~(ciphertexts : EOS.ext_occs)
    ~(enc_f : Symbols.fname) (* encryption function *)
    ~(retry : unit -> ROS.simple_occs)
    ~(rec_call : O.pos_info -> Term.term -> ROS.simple_occs)
    (info : O.pos_info)
    (t : term) 
  : ROS.simple_occs
  =
  (* handles a few cases, using [rec_call] for rec calls on subterms,
     and calls [retry] for the rest *)
  (* add variables from fv (ie bound above where we're looking)
     to env with const tag. *)
  let env =
    let vars = 
      Vars.add_vars (Vars.Tag.global_vars ~const:true info.pi_vars) env.vars 
    in
    Env.update ~vars env
  in

  match t with
  | _ when HighTerm.is_ptime_deducible ~si:false env t -> []
  (* SI not needed here *)

  (* non ptime deterministic variable -> forbidden *)
  | Var v ->
    Tactics.soft_failure
      (Tactics.Failure 
         (Fmt.str "terms contain a non-ptime variable: %a" Vars.pp v))

  (* A name [rr'] -> 
     check if it is an occurrence of the [rr] in a [enc(mm,rr,kk)]
     in [ciphertexts]. *)
  | Name (_, rrargs') as rr' ->
    let rr' = Name.of_term rr' in
    (* Find all randoms in [ciphertexts] it could be an occurrence of *)
    let occs =
      List.filter_map
        (fun (ceo:EOS.ext_occ) ->
           let co = ceo.eo_occ in
           let rr = 
             match co.so_ad with 
             | DataCiphertext d -> d.rand 
             | _ -> assert false 
           in
           if rr.symb.s_symb = rr'.symb.s_symb then (* found an rr w/ the same 
                                                       symbol -> occ *)
             Some
               (mk_randomness_occ
                  ~content:rr'
                  ~vars:info.pi_vars
                  ~cond:info.pi_cond
                  ~typ:info.pi_occtype
                  ~sub:info.pi_subterm
                  ~ciphertext:ceo
                  ~plain:None
                  ~key:None)
           else 
             None)
        ciphertexts
    in

    (* Also recurse in the arguments *)
    let occs' = List.concat_map (rec_call info) rrargs' in
    occs @ occs'


  (* A random value [rr'] occurring in [enc(mm',rr',kk')]
     when [kk'] is potentially in equal to [k] (ie has the same symbol). *)
  | App (Fun (f, _), 
         [Tuple [mm'; (Name (_, rrargs') as rr'); (Name (kksb', _) as kk')]])
    when enc_f = f && kksb'.s_symb = k.symb.s_symb ->
    let rr' = Name.of_term rr' in
    let kk' = Name.of_term kk' in

    (* Find all randoms in [ciphertexts] [rr'] could be an occurrence of *)
    let occs =
      List.filter_map
        (fun (ceo:EOS.ext_occ) ->
           let co = ceo.eo_occ in
           let rr = 
             match co.so_ad with 
             | DataCiphertext d -> d.rand 
             | _ -> assert false 
           in
           if rr.symb.s_symb = rr'.symb.s_symb then (* found an rr w/ the same 
                                                       symbol -> occ *)
             Some
               (mk_randomness_occ
                  ~content:rr'
                  ~vars:info.pi_vars
                  ~cond:info.pi_cond
                  ~typ:info.pi_occtype
                  ~sub:info.pi_subterm
                  ~ciphertext:ceo
                  ~plain:(Some mm')
                  ~key:(Some kk'))
           else 
             None)
        ciphertexts
    in

    (* Also recurse on mm', kk' (kk' could itself be a forbidden rr), 
       rrargs' *)
    let occs' = List.concat_map (rec_call info) 
        (mm' :: (Name.to_term kk') :: rrargs') in
    occs @ occs'

  | _ -> retry ()


