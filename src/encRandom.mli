(** Auxiliary functions to generate random freshness conditions. 
    Built using NameOccs, used for int-ctxt and ind-cca. *)
open Term

module Args = TacticsArgs
module L = Location
module SE = SystemExpr
module NO = NameOccs

module TS = TraceSequent

module Hyps = TS.LocalHyps

module Name = NameOccs.Name

type sequent = TS.sequent

type lsymb = Theory.lsymb

module MP = Match.Pos
module Sp = MP.Sp


(** Auxiliary function to check if a name with the same 
   symbol as n occurs in t (without expanding macros) *)
val has_name : Name.t -> term -> bool


(** Occurrence of a ciphertext enc(m,r,k1)
    with some key k1 with the same symbol as kcoll.
    Additionally in 'b we store (m,r,k1,kcoll)
    so that we won't need to compute them again later. *)
type ctxt_aux = { 
  ca_m     : term ; 
  ca_r     : Name.t ; 
  ca_k1    : Name.t ; 
  ca_kcoll : Name.t ;
}

type ctxt_occ = (term, ctxt_aux) NO.simple_occ
type ctxt_occs = ctxt_occ list

type ectxt_occ = (term, ctxt_aux) NO.ext_occ
type ectxt_occs = ectxt_occ list
    


(** Randomness occurrence.
    'a is Name.t, for the name r' which is the occurrence
    'b contains a ectxt_occ, which is the occ enc(m,r,k1) where
    the r that r' collides with was found,
    and optionally a pair [(m',k'):term * Name.t] for the
    case where r' was found in enc(m',r',k').
*)
type rand_occ = (Name.t, (ectxt_occ * (term * Name.t) option)) NO.simple_occ
type rand_occs = rand_occ list



(*------------------------------------------------------------------*)
(** Look for occurrences using NameOccs *)

type dec_allowed = Allowed | NotAllowed | NotAbove of Name.t


(** Finds occs of k, except those that are
    - in enc key position (if pkf = None)
    - in pub key position (if pkf <> None)
    - in dec key position depending on dec_allowed:
      -> if dec_allowed = Allowed: ignore these occs
      -> if dec_allowed = NotAllowed: count these occs
      -> if dec_allowed = NotAbove x: ignore these occs, unless x occurs in
          the ciphertext or the indices of the decryption key
    - under a hash, if hashf <> None
      (this is a special case only used for Charlie's sus assumption).
    Also finds all occs of names in rs, in any position. 
    returns additionally all occs of ciphertexts
    encrypted with (potentially) k, when pkf = None
    (for pub key encryption there is no integrity guarantee,
     so no need to collect the ciphertexts) *)
val get_bad_occs_and_ciphertexts :
  Env.t -> (* initial environment  *)
  Name.t -> (* key k to look for *)
  Name.t list -> (* randoms to look for *)
  term -> (* ciphertext c in dec(c,k) <> fail *)
  Symbols.fname -> (* encryption function *)
  Symbols.fname -> (* decryption function *)
  ?hash_f:Symbols.fname option -> (* hash function,
                                     when one is defined together w/ enc *)
  ?pk_f:Symbols.fname option -> (* public key function, when
                                         using asymmetric encryption *)
  dec_allowed:dec_allowed ->
  (unit -> NO.n_occs * ctxt_occs) ->
  (fv:Vars.vars ->
   cond:terms ->
   p:MP.pos ->
   info:NO.expand_info ->
   st:term ->
   term ->
   NO.n_occs * ctxt_occs) ->
  info:NO.expand_info ->
  fv:Vars.vars ->
  cond:terms ->
  p:MP.pos ->
  st:term ->
  term ->
  NO.n_occs * ctxt_occs


(** Look for bad uses of the randoms r from the list of
    ciphertexts occurrences enc(m,r,k1). 
    ie - if r occurs somewhere not as r' in enc(m',r', k'):
           bad occ if k1 = k and r' = r
    - if r occurs as r' in enc(m',r',k'):
           bad occ if k1 = k and r' = r and (m' <> m or k' <> k).
    Only used for symmetric encryption: for asym enc, the adversary
    has the public key and can thus encrypt anything *)
val get_bad_randoms :
  Env.t ->
  Name.t ->
  ectxt_occs ->
  Symbols.fname -> (* encryption function *)
  (unit -> NO.n_occs * rand_occs) ->
  (fv:Vars.vars ->
   cond:terms ->
   p:MP.pos ->
   info:NO.expand_info ->
   st:term ->
   term ->
   NO.n_occs * rand_occs) ->
  info:NO.expand_info ->
  fv:Vars.vars ->
  cond:terms ->
  p:MP.pos ->
  st:term ->
  term -> 
  NO.n_occs * rand_occs 


(** Constructs the formula expressing that a ciphertext occurrence
    c'=enc(m',r',k1) is indeed in collision with c, and k1 with k.
    used for integrity: if dec(c, k) succeeds, then c must be
    equal to (one of the) c'=enc(m',r',k1) for which k1 = k.
    (note that c is not necessarily syntactically an encryption with k,
    so c = c' is not sufficient: it doesn't necessarily mean that k = k1) *)
val ciphertext_formula :
    negate : bool ->
    term ->
    term ->
    ctxt_aux ->
    term


                                          
(** Constructs the formula expressing that an occurrence of a random r'
    is indeed a bad occurrence of the r from the ctxt_occ enc(m,r,k1),
    given that the key we're interested in is k:
    - if r' was found in enc(m',r',k'):
       phi_time(r) && k1 = k && r' = r && (k' <> k || m' <> m)
     or the negative phi_time(r) => k1 = k => r' = r => k' = k && m' = m
    - if r' was found directly:
       phi_time(r) && k1 = k && r' = r
     or the negative phi_time(r) => k1 = k => r' = r => false.
 note that it does not include the phi_time for r',
    as this is handled by NameOccs.
    similarly, no need to worry about the conditions or vars,
    as they were all added to the cond by mk_rand *)
val randomness_formula :
  ?use_path_cond : bool ->
  negate : bool ->
  Name.t ->
  Name.t ->
  ectxt_occ * (term * Name.t) option ->
  (* eco: occ where r was, omk = option (m',k') *)
  term
