(*******************************************************************************
# A Simple Stateful Protocol

 In this file, we present a simple stateful cryptographic protocol. Showing 
 that such protocols are secure often require proving invariants on the
 state of the protocol agents.
*******************************************************************************)

include Basic.

(* ----------------------------------------------------------------- *)
(** ## Ciphertext integrity (INT-CTXT) *)

(* We consider symmetric encryption an decryption functions `enc` and `dec`. 
   These functions are assumed to satisfy the INT-CTXT cryptographic 
   assumption: essentially, it is not possible for the adversary to 
   produce a message `m` that decrypts correctly (i.e. `dec(m,k) <> fail`).
   Moreover, this holds even if the adversary has access to an encryption 
   oracle, by adding the requirement that the message `m` produced by the
   adversary cannot be the result of a call to the encryption oracle. *)
senc enc, dec.

(* ----------------------------------------------------------------- *)
(** ## Using INT-CTXT  
    This assumption can be exploited using the `intctxt` tactic. Check 
    how this is done in the example below. *)

(* a constants `a` and `b` *)
abstract a : message.

(* a key `k` and an encryption randomness `r` *)
name k : message.
name r : message.

system [example] null.

goal [example] _ : 
  dec(att(enc(a,r,k)), k) <> fail => 
  att(enc(a,r,k)) = enc(a,r,k).
Proof.
  intro H.
  intctxt H. 
  auto. 
Qed.
 
(* ----------------------------------------------------------------- *)
(** ## declarations *)

abstract ok : message
abstract ko : message

(* `key(i)` is the key of the tag with identity `i` *)
name key : index -> message

(* ----------------------------------------------------------------- *)
(* We can declare persistent memory cells using the `mutable` keyword. 
   Here, we consider two counters, a tag counter and a reader counter. 
   Moreover, each counter is indexed by the identities of the tag 
   holding it. *)

(* stateful counter stored by the tags *)
mutable cpt (i : index) : message = zero.

(* stateful counter stored by the reader *)
mutable Rcpt (i : index) : message = zero.

(* ----------------------------------------------------------------- *)
(* operators over counter values *)

(* integer increment *)
abstract incr : message -> message.

(* Strict ordering over messages
   Note the parenthesis around `(~<)`, which declare that `~<` is an 
   _infix_ operator. *)
abstract (~<) : message -> message -> boolean.

(* ----------------------------------------------------------------- *)
(* channel for tag messages *)
channel cT

(* channel for reader messages *)
channel cR.

(* ----------------------------------------------------------------- *)
(** ## axioms: decryption/encryption *)

(* functional correctness of decryption and encryption *)
axiom [any] dec_enc (x, y, z : message) : dec(enc(x,y,z),z) = x.

(* ----------------------------------------------------------------- *)
(** ## strict ordering
     
    We assume that `~<` is a transitive and strict relation *)

axiom [any] order_trans (n1,n2,n3:message):
  n1 ~< n2 => n2 ~< n3 => n1 ~< n3.

axiom [any] order_strict (n1,n2:message):
  n1 = n2 => n1 ~< n2 => false. 

(* We require that `~<` and `incr` interact as expected *)
axiom [any] order_incr (n1,n2:message):
  n1 = n2 => n1 ~< incr(n2).

(* ----------------------------------------------------------------- *)
(** ## non-strict version of the ordering *)

(* We introduce the non-strict version of `~<`.
   Instead of doing this using an `abstract`, we use an operator 
   declaration starting with the `op` keyword.
   An operator is a function symbols whose implementation is known.
   In a proof script, an operator definition can be unfolded using 
   the same mechanisms than for macros, e.g. `rewrite /(~~<)`. *)
op (~~<) (x : message, y : message) : boolean = x ~< y || x = y.

(* We now prove a few properties of `~~<` and `~<` *)
goal [any] le_lt (n1,n2 : message):
  n1 ~< n2 => n1 ~~< n2.
Proof. 
  by intro ?; rewrite /(~~<); left. 
Qed.

goal [any] le_lt_trans (n1,n2,n3 : message):
  n1 ~~< n2 => n2 ~< n3 => n1 ~< n3.
Proof.
  rewrite !/(~~<) => H1 H2.
  case H1.
  + by apply order_trans _ n2.
  + by rewrite H1. 
Qed.

goal [any] lt_le_trans (n1,n2,n3 : message):
  n1 ~< n2 => n2 ~~< n3 => n1 ~< n3.
Proof.
  rewrite !/(~~<) => H1 H2.
  case H2.
  + by apply order_trans _ n2.
  + by rewrite -H2. 
Qed.

(* Prove, using `order_trans`, that `~~<` is also
   a transitive relation. *)
goal [any] le_trans (n1,n2,n3 : message):
  n1 ~~< n2 => n2 ~~< n3 => n1 ~~< n3.
Proof. 
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(* we assume that the constant `fail` is different from `zero` *)
axiom [any] zero_ne_fail : zero <> fail.

(* similarly, we assume that increasing a value `x` cannot yield `fail` *)
axiom [any] incr_ne_fail (x : message): incr(x) = fail => false.

(* ----------------------------------------------------------------- *)
(** ## Processes *)

(* session number `k` of the RFID tag with identity `i` *)
process tag(i : index, k : index) =
  cpt(i) := incr(cpt(i));
  new n;
  T: out(cT, enc(cpt(i), n, key(i))).

(* session number `j` of the reader R trying to authenticate tag `i` *)
process reader(j : index, i : index) =
  in(cT,x);
  let cI = dec(x, key(i)) in
  let c = Rcpt(i) in
  if cI <> fail && c ~< cI then
    Rcpt(i) := cI;
    R: out(cR, ok)
  else R1: out(cR, ko).

system (
  (!_j !_i reader(j,i) ) | 
  (!_i !_k    tag(i,k) ) 
).

(* ----------------------------------------------------------------- *)
(** ## Authentication *)

(* prove that our protocol satisfies the following authentication 
   property *)
goal authentication_R (j, i : index[const]) :
  happens(R(j,i)) =>
  cond@R(j,i) <=>
  exists (k : index),
    T(i,k) < R(j,i) &&
    output@T(i,k) = input@R(j,i) &&
    Rcpt(i)@pred(R(j,i)) ~< cpt(i)@T(i,k).
Proof.
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Some counter properties *)

 (* The tag counter is not decreasing *)
goal counter_increaseT (i : index, tau1, tau2 : timestamp):
  tau1 <= tau2 => 
  exec@tau2 =>
  cpt(i)@tau1 ~~< cpt(i)@tau2.
Proof. 
  admit. (* TODO *)
Qed.

(* the tag counter is strictly increasing when a tag session occurs. *)
goal counter_increaseT_strict (tau1, tau2 : timestamp, i,k : index):
  exec@tau2 =>
  tau1 < T(i,k) => 
  T(i,k) <= tau2 =>
  cpt(i)@tau1 ~< cpt(i)@tau2.
Proof.
  admit. (* TODO *)
Qed.

 (* The reader counter is not decreasing *)
goal counter_increaseR (i : index, tau1, tau2 : timestamp):
  tau1 <= tau2 => 
  exec@tau2 =>
  Rcpt(i)@tau1 ~~< Rcpt(i)@tau2.
Proof. 
  admit. (* TODO *)
Qed.


(* Show, using `counter_increaseT_strict`, that if the tag counter of
   tag `i` did not increase between two sessions `k` and `k1`,
   then `k = k1`. 
   Hint: do a case analysis on the order in which `T(i,k)` and 
   `T(i,k1)` occur. *)
goal tag_cpt_strict (i, k, k1: index) :
  happens(T(i,k1), T(i,k)) =>
  cpt(i)@T(i,k) = cpt(i)@T(i,k1) =>
  exec@T(i,k) =>
  exec@T(i,k1) =>
  k = k1.
Proof.
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Intermediary lemma on tag outputs *)

(* Show using the `intctxt` tactic that if two tags outputs are equal, 
   then they must have the same identities.
   Hint: you may use the `incr_ne_fail` axiom above *)
goal tag_output_collision (i, i1, k, k1: index[const]) :
  happens(T(i,k), T(i1,k1)) =>
  output@T(i1,k1) = output@T(i,k) =>
  i = i1.
Proof.
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Injective authentication *)

(* [Advanced] Show that our protocol provides injective authentication using 
   the lemmas above. *)
goal injective_authentication (j, i, j1, i1 : index[const]) :
  R(j,i) < R(j1,i1) =>
  exec@R(j,i) =>
  exec@R(j1,i1) =>
  input@R(j,i) = input@R(j1,i1) =>
  i = i1 && j = j1.
Proof.
  admit. (* TODO *)
Qed.
