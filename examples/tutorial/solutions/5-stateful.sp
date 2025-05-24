(*******************************************************************************
# A Simple Stateful Protocol

 In this file, we present a simple stateful cryptographic protocol. Showing 
 that such protocols are secure often require proving invariants on the
 state of the protocol agents.
*******************************************************************************)

include Core.

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

system example = null.

lemma [example] _ : 
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
lemma [any] tt_le_lt (n1,n2 : message):
  n1 ~< n2 => n1 ~~< n2.
Proof. 
  by intro ?; rewrite /(~~<); left. 
Qed.

lemma [any] tt_le_lt_trans (n1,n2,n3 : message):
  n1 ~~< n2 => n2 ~< n3 => n1 ~< n3.
Proof.
  rewrite !/(~~<) => H1 H2.
  case H1.
  + by apply order_trans _ n2.
  + by rewrite H1. 
Qed.

lemma [any] tt_lt_le_trans (n1,n2,n3 : message):
  n1 ~< n2 => n2 ~~< n3 => n1 ~< n3.
Proof.
  rewrite !/(~~<) => H1 H2.
  case H2.
  + by apply order_trans _ n2.
  + by rewrite -H2. 
Qed.

(* Prove, using `order_trans`, that `~~<` is also
   a transitive relation. *)
lemma [any] tt_le_trans (n1,n2,n3 : message):
  n1 ~~< n2 => n2 ~~< n3 => n1 ~~< n3.
Proof. 
  (* BEGIN EXO *) 
  rewrite /(~~<) => H1 H2. 
  case H1; case H2. 
  + by left; apply order_trans _ n2.
  + by rewrite -H2; left. 
  + by rewrite H1; left. 
  + by right. 
 (* END EXO *)
Qed.

(* ----------------------------------------------------------------- *)
(* we assume that the constant `fail` is different from `zero` *)
axiom [any] zero_ne_fail : zero <> fail.

(* similarly, we assume that increasing a value `x` cannot yield `fail` *)
axiom [any] incr_ne_fail (x : message): incr(x) = fail => false.

(* ----------------------------------------------------------------- *)
(** ## Processes *)

mutex lT:1.
mutex lR:1.
(* session number `k` of the RFID tag with identity `i` *)
process tag(i : index, k : index) =
  lock lT(i);
  cpt(i) := incr(cpt(i));
  new n;
  T: out(cT, enc(cpt(i), n, key(i)));
  unlock lT(i).

(* session number `j` of the reader R trying to authenticate tag `i` *)
process reader(j : index, i : index) =
  in(cT,x);
  lock lR(i);
  let cI = dec(x, key(i)) in
  let c = Rcpt(i) in
  if cI <> fail && c ~< cI then
    Rcpt(i) := cI;
    R: out(cR, ok); unlock lR(i)
  else R1: out(cR, ko); unlock lR(i).

system (
  (!_j !_i reader(j,i) ) | 
  (!_i !_k    tag(i,k) ) 
).

(* ----------------------------------------------------------------- *)
(** ## Authentication *)

(* prove that our protocol satisfies the following authentication 
   property *)
lemma authentication_R (j, i : index[const]) :
  happens(R(j,i)) =>
  cond@R(j,i) <=>
  exists (k : index),
    T(i,k) < R(j,i) &&
    output@T(i,k) = input@R(j,i) &&
    Rcpt(i)@pred(R(j,i)) ~< cpt(i)@T(i,k).
Proof.
  (* BEGIN EXO *)
  intro Hap.
  rewrite /cond.
  split.

  + intro [H1 H2].
    rewrite /cI in H1.
    intctxt H1.
    (* ciphertext *)
    intro [k [_ Eq]]. 
    rewrite /cI /c Eq dec_enc in H2. 
    by exists k. 

  + intro [k [Ht Eq Hc]].
    rewrite /cI -Eq dec_enc //=. 
    rewrite /cpt => V.
    by apply incr_ne_fail in V. 
 (* END EXO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Some counter properties *)

 (* The tag counter is not decreasing *)
lemma counter_increaseT (i : index, tau1, tau2 : timestamp):
  tau1 <= tau2 => 
  cpt(i)@tau1 ~~< cpt(i)@tau2.
Proof. 
  (* BEGIN EXO *)
  induction tau2 => tau2 IH E.
  case tau2 => //. 

  (* R(j,i0) *)
  + intro [j i0 Eq].
    rewrite /cpt.
    case (tau1 = tau2) => ?; 1: by rewrite /(~~<); right.
    by apply IH => //.

  (* R1(j,i0) *)
  + intro [j i0 Eq].
    rewrite /cpt.
    case (tau1 = tau2) => ?; 1: by rewrite /(~~<); right.
    by apply IH => //.

  (* T(i0,k) *)
  + intro [i0 k Eq].
    rewrite /cpt.
    case (tau1 = tau2) => ?; 1: by rewrite /(~~<); right.
    case (i = i0) => ? //=; 2: by apply IH.
    apply tt_le_trans _ (cpt(i)@pred(tau2)) => //.
    - by apply IH.        
    - by rewrite /(~~<); left; apply order_incr.
  (* END EXO *)
Qed.

(* the tag counter is strictly increasing when a tag session occurs. *)
lemma counter_increaseT_strict (tau1, tau2 : timestamp, i,k : index):
  tau1 < T(i,k) => 
  T(i,k) <= tau2 =>
  cpt(i)@tau1 ~< cpt(i)@tau2.
Proof.
  (* BEGIN EXO *)
  intro H2 H3. 
  apply tt_le_lt_trans _ (cpt(i)@pred(T(i,k))).
  + by apply counter_increaseT.
  + apply tt_lt_le_trans _ (cpt(i)@T(i,k)).
    - rewrite /cpt.
      by apply order_incr.
    - by apply counter_increaseT.
  (* END EXO *)
Qed.

 (* The reader counter is not decreasing *)
lemma counter_increaseR (i : index, tau1, tau2 : timestamp):
  tau1 <= tau2 => 
  exec@tau2 =>
  Rcpt(i)@tau1 ~~< Rcpt(i)@tau2.
Proof. 
  (* BEGIN EXO *)
  induction tau2 => tau2 IH Le E.
  case tau2 => //. 

  (* R(j,i0) *)
  + intro [j i0 Eq].
    rewrite /Rcpt.
    case (tau1 = tau2) => ?; 1: by rewrite /(~~<); right.
    case (i = i0) => ? //=; 2: by apply IH.
    rewrite /exec /cond /c in E. 
    apply tt_le_trans _ (Rcpt(i)@pred(tau2)) => //.
    by apply IH.        

  (* R1(j,i0) *)
  + intro [j i0 Eq].
    rewrite /Rcpt.
    case (tau1 = tau2) => ?; 1: by rewrite /(~~<); right.
    case (i = i0) => ? //=; 2: by apply IH.
    rewrite /exec /cond /c in E. 
    apply tt_le_trans _ (Rcpt(i)@pred(tau2)) => //.
    - by apply IH.        

  (* T(i0,k) *)
  + intro [j0 k Eq].
    rewrite /Rcpt.
    case (tau1 = tau2) => ?; 1: by rewrite /(~~<); right.
    by apply IH => //.
  (* END EXO *)
Qed.


(* Show, using `counter_increaseT_strict`, that if the tag counter of
   tag `i` did not increase between two sessions `k` and `k1`,
   then `k = k1`. 
   Hint: do a case analysis on the order in which `T(i,k)` and 
   `T(i,k1)` occur. *)
lemma tag_cpt_strict (i, k, k1: index) :
  happens(T(i,k1), T(i,k)) =>
  cpt(i)@T(i,k) = cpt(i)@T(i,k1) =>
  k = k1.
Proof.
  (* BEGIN EXO *)
   intro *. 
   have A : T(i,k) < T(i,k1) || T(i,k) > T(i,k1) || k = k1 by auto.
   case A => //.
   - have Xa := counter_increaseT_strict (T(i,k)) (T(i,k1)) i k1. 
     by apply order_strict in Xa.
   - have Xa := counter_increaseT_strict (T(i,k1)) (T(i,k)) i k. 
     by apply order_strict in Xa.
  (* END EXO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Intermediary lemma on tag outputs *)

(* Show using the `intctxt` tactic that if two tags outputs are equal, 
   then they must have the same identities.
   Hint: you may use the `incr_ne_fail` axiom above *)
lemma tag_output_collision (i, i1, k, k1: index[const]) :
  happens(T(i,k), T(i1,k1)) =>
  output@T(i1,k1) = output@T(i,k) =>
  i = i1.
Proof.
  (* BEGIN EXO *)
  intro H H2.
  rewrite /output in H2.
  have V:
    cpt(i)@T(i,k) =
    dec(enc(cpt(i1)@T(i1,k1),n(i1,k1),key(i1)), key(i)) by auto. 
  intctxt V => //.
  intro @/cpt U. 
  by apply incr_ne_fail in U.
  (* END EXO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Injective authentication *)

(* [Advanced] Show that our protocol provides injective authentication using 
   the lemmas above. *)
lemma injective_authentication (j, i, j1, i1 : index[const]) :
  R(j,i) < R(j1,i1) =>
  exec@R(j,i) =>
  exec@R(j1,i1) =>
  input@R(j,i) = input@R(j1,i1) =>
  i = i1 && j = j1.
Proof.
  (* BEGIN EXO *)
  intro Hap. 
  intro S1 S2.
  have H1 : cond@R(j,i) by auto.
  have H2 : cond@R(j1,i1) by auto.
  revert H2 H1. 
  rewrite !authentication_R //=.
  intro [k [H1 H2 H3]] [k1 [G1 G2 G3]] U.
  rewrite U -G2 /output in H2.

  (* since the tag outputs collide, we know that they have the
     same identities. *)
  have A : i = i1 by apply tag_output_collision i i1 k k1. 
  rewrite -A /= in *; clear A.  

  (* consequence of `counter_increaseT` *)
  have ?: cpt(i)@T(i,k) = cpt(i)@T(i,k1) by auto.
  have A: k = k1. {. 
    by apply tag_cpt_strict i k k1.
  }.
  rewrite -A in *; clear A.

  have B := counter_increaseR i (R(j,i)) (pred(R(j1,i))) _ _; 1,2:auto.
  have A : Rcpt(i)@R(j,i) = cpt(i)@T(i,k) by auto.

  clear S1 S2 U G2. 
  clear H3 G1 H1 Hap.
  rewrite /(~~<) in B. 
  case B.
  + rewrite -A in G3. 
    have U := order_trans _ _ _ B G3. 
    by apply order_strict in U.
  + rewrite -A B in G3.
    by apply order_strict in G3.
 (* END EXO *)
Qed.
