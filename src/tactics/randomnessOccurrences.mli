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

(** We instantiate it twice: first to search for bad uses of the key
    and randomness from the challenge ciphertext, as well as to find
    all encryptions with that key, and second to check that encryption
    randomness is used injectively. *)


(** We search at the same time for bad ocurrences of the key,
    of randomness, and for ciphertexts with the key.
    It's safer to do all three at the same time, so we know for sure
    that we do not miss any occurrence (eg, an occurrence that is for instance
    not considered as a bad key occ will lead to a ciphertext occ).
    In the ciphertext case:
    we only want to collect all ciphertexts in a term that use
    a given key, but not generate formulas about them.
    We use NoCipher as a dummy collision value (it can only be used
    as collision, not as the occurrence content). *)
type enc_content =
  | BadName of name
  | Ciphertext of term
  | NoCipher


(** Additional data for ciphertext occurrences:
    for an occurrence enc(msg, rand, key) (symmetric)
    or aenc(msg, rand, pk(key)) (asymmetric)
    that was found when searching for
    encryptions with keycoll, we store msg, rand, key, keycoll. *)
type enc_data =
  | DataCiphertext of {msg:term; rand:name; key:name; keycoll:name}
  | NoData


(** Occurrences instantiation for the encryption search *)
module EncryptionOC : O.OccContent
  with type content = enc_content
   and type data = enc_data

module EncryptionOS : O.OccurrenceSearch
    with module EO.SO.OC = EncryptionOC

module EncryptionOF : O.OccurrenceFormulas
  with type ext_occ = EncryptionOS.ext_occ


(** In the symmetric case, when considering a ciphertext [c = enc(m,r,k)],
    we need to search for bad ocurrences of all randoms
    that are used to encrypt using key [k].
    Once we obtain the list of ciphertexts [cc = enc(mm,rr,kk)]
    where [kk] and [k] have the same symbol (and thus could be equal),
    we will search for occurrences [rr'] of each [rr]:
    - as encryption randomness in [cc' = enc(mm', rr', kk')], 
      where [kk'] and [kk] have the same symbol: then we have a collision if 
      [kk = k /\ rr' = rr /\ (mm' <> mm \/ kk' <> kk)]
    - in any other position: then we have a collision if
      [kk = k /\ rr' = rr] *)

(** We do not use the normal name occurrence, as we need additional data:
    the content is the name [rr']
    the data is - the ciphertext [cc = enc(mm,rr,kk)] and its associated data
    (where [rr], which will be the collision value, comes from)
    - if [rr'] was found in [cc' = enc(mm',rr',kk')], 
                  the plaintext [mm'] and the key [kk'] *)
type rand_content = name
type rand_data = 
  { cipher:enc_content; 
    cipherdata:enc_data; 
    plain: term option; 
    key: name option }


(** Occurrences instantiation for the randomness search *)
module RandomnessOC : O.OccContent
  with type content = rand_content
   and type data = rand_data

module RandomnessOS : O.OccurrenceSearch
  with module EO.SO.OC = RandomnessOC 

module RandomnessOF : O.OccurrenceFormulas
  with type ext_occ = RandomnessOS.ext_occ


(** Constructs a randomness occurrence using the ext_occ of the
    ciphertext from which the random we were looking for came. 
    This way we can add the ciphertext occ's variables and condition 
    to the randomness occ. *)
val mk_randomness_occ :
  content:RandomnessOC.content -> vars:Vars.vars -> cond:terms ->
  typ:O.occ_type -> sub:term ->
  ciphertext:EncryptionOS.EO.ext_occ -> plain:term option -> key:name option ->
  RandomnessOS.EO.SO.simple_occ



(*------------------------------------------------------------------*)
(* Look for occurrences using the Occurrences module *)

(** A flag indicating whether decryption is allowed or not when looking
    for occurrences of the key *)
type dec_allowed = Allowed | NotAllowed | NotAbove of name

(** Checks whether decrypting a term with subterms ts is allowed *)
val is_dec_allowed : dec_allowed -> Term.terms -> bool

(** The [EncryptionOS.f_fold_occs] function used depends on the tactic,
    we do not have a generic one. *)

(** A [RandomnessOS.f_fold_occs] function.
    Looks for bad uses of the randoms used in all ciphertexts from the list 
    of occurrences [ciphertexts] obtained when looking for enc with [k].
    As described above, only relevant in the symmetric case.
    Any occurrence of a random is bad, except as encryption randomness
    with the same plain and key.   *)
val get_bad_randoms :
  Env.t ->
  k:name -> ciphertexts:EncryptionOS.ext_occs ->
  enc_f:Symbols.fname ->
  RandomnessOS.f_fold_occs
