(*******************************************************************************
# Cryptographic primitives : encryption

  An encryption scheme with public key `pk(n)` and secret key `n` is
  indistinguishable against chosen cipher-text attacks (IND-CCA1) iff. 
  for every PPTM `A` with access to

  - a left-right oracle `O_LR^b` (where `b \in {0,1}`) defined by

    * `O_LR^b(m1, m2) := enc(mb, r, pk(n))`      (if `len(m1) =  len(m2)`)
      (where `r` is a fresh randomness)

    * `O_LR^b(m1, m2) := 0`                      (if `len(m1) <> len(m2)`)
  
  - and a decryption oracle `O_dec`
      `O_dec(x) := dec(x, n)`
  
  where `A` can call `O_LR` once, and cannot call `O_dec` after `O_LR`, 
  we have that
    |   Pr(A(O_LR^1, O_dec, pk(n)) = 1) 
      - Pr(A(O_LR^0, O_dec, pk(n)) = 1) |
  is negligible, where `n` is drawn uniformly at random.
*******************************************************************************)

(* ----------------------------------------------------------------- *)
(* Questions:
   - why do we forbid the adversary to call `O_LR` after `O_dec`? 
   - why does the `O_LR` oracle check that `len(m1) =  len(m2)`? *)


(* ----------------------------------------------------------------- *)
(** ## IND-CCA1 Security in Squirrel *)

include Basic.

(* ----------------------------------------------------------------- *)
system null.

(* ----------------------------------------------------------------- *)
(** ## Preliminaries *)

(* To start, we need a few declarations and assumptions. *)

abstract a : message.
abstract b : message.

(* We introduce a constant for representing the security parameter, in unary. *)
abstract eta : message.

(* We then assume that this constant is the length of `a` and `b`. *)
axiom [any] len_a : len(a) = eta.
axiom [any] len_b : len(b) = eta.
hint rewrite len_a.
hint rewrite len_b.

(* The following lemma state that `diff` and `len` commutes.
   We will use it later. *)
goal len_diff (x,y : message) : len(diff(x,y)) = diff(len(x), len(y)).
Proof.  
  project. 
  - auto.
  - auto.
Qed.


(* ----------------------------------------------------------------- *)
(** ## Exercises *)

(* we declare an asymmetric encryption schema with encryption 
   function `enc`, decryption `dec`, and public key `pk`. *)
aenc enc, dec, pk.

(* the secret key *)
name n : message.

(* we declare a couple of encryption randomness *)
name r0 : message.
name r1 : message.

(* The `cca1` tactic allows to exploit the IND-CCA1 assumption.
   Check how we use it below. *)
global goal enc_0 : 
  equiv(
    pk(n), 
    diff(enc(a, r0, pk(n)), enc(b, r0, pk(n)))
  ).
Proof.
  cca1 1.
  + auto. 
  + rewrite len_diff len_a len_b.
    refl.
Qed.

(* Which of the following formulas can be proven using `cca1`?
   For each formula, explain why it is a consequence of the 
   IND-CCA1 game, or why the IND-CCA1 game does not apply.
   Then, if the former case, prove it using the `cca1` tactic.  *)
global goal enc_1 : 
  equiv(
    pk(n), 
    diff(enc(a, r0, pk(n)), (* *) enc(b, r0, pk(n))),
    diff(enc(a, r1, pk(n)), (* *) enc(a, r1, pk(n)))
  ).
Proof.
  admit. (* TODO *)
Qed.

global goal enc_2 : 
  equiv(
    pk(n), 
    diff(enc(a, r0, pk(n)), (* *) enc(b, r0, pk(n))),
    diff(enc(a, r0, pk(n)), (* *) enc(a, r0, pk(n)))
  ).
Proof.
  admit. (* TODO *)
Qed.

global goal enc_3 : 
  equiv(
    pk(n), 
    diff(enc(a, r0, pk(n)), (* *) enc(n, r0, pk(n)))
  ).
Proof.
  admit. (* TODO *)
Qed.
