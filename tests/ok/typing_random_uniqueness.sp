(* This file tests the tactics `typing`.
   If a term uses twice the same random for encryption,
   it must encrypt the same message.
   This file defines systems for:
   - Two randoms for two different messages (should be ok)
   - One random for the same message twice (should be ok)
   - One random for two different message (should fail)
   - One random for two different messages in two different actions (should fail)
   - One random for two different messages in two mutable updates (should fail)
   Tests are performed for symmetric and assymetric encryption. *)

set securityTypes = true.

channel c
senc symenc,sdec
aenc asymenc,adec,pk
name k : message, SK[symenc, Low]
name sk : message, AK[asymenc, Low]
abstract a : message
abstract b : message
name r1 : message, Rand
name r2 : message, Rand
mutable s1 : message, Low = empty
mutable s2 : message, Low = empty.

system sys1 = (in(c, x); out(c,<symenc(a,r1,k), symenc(b,r2,k)>)).
system sys2 = (in(c, x); out(c,<symenc(a,r1,k), symenc(a,r1,k)>)).
system sys3 = (in(c, x); out(c,<symenc(a,r1,k), symenc(b,r1,k)>)).
system sys4 = (in(c, x); out(c,symenc(a,r1,k)); out(c,symenc(b,r1,k))).
system sys5 = (in(c, x); s1 := symenc(a,r1,k); s2 := symenc(b,r1,k); out(c,empty)).
system sys6 = (in(c, x); out(c,<asymenc(a,r1,pk(sk)), asymenc(b,r2,pk(sk))>)).
system sys7 = (in(c, x); out(c,<asymenc(a,r1,pk(sk)), asymenc(a,r1,pk(sk))>)).
system sys8 = (in(c, x); out(c,<asymenc(a,r1,pk(sk)), asymenc(b,r1,pk(sk))>)).
system sys9 = (in(c, x); out(c,asymenc(a,r1,pk(sk))); out(c,asymenc(b,r1,pk(sk)))).
system sys10 = (in(c, x); s1 := asymenc(a,r1,pk(sk)); s2 := asymenc(b,r1,pk(sk)); out(c,empty)).

(* The tactic typing must succeed only in well-typed systems:
   [sys1], [sys2], [sys6], and [sys7].*)

name h : message, High
name l : message, Low.
lemma[sys1] _ : h=l => false.
Proof.
  intro H.
  typing H.
Qed.
lemma[sys2] _ : h=l => false.
Proof.
  intro H.
  typing H.
Qed.
lemma[sys3] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys4] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys5] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys6] _ : h=l => false.
Proof.
  intro H.
  typing H.
Qed.
lemma[sys7] _ : h=l => false.
Proof.
  intro H.
  typing H.
Qed.
lemma[sys8] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys9] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys10] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
