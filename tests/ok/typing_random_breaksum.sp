(* This file tests the tactics `typing`.
   Typing may break sum types (e.g. [Cst a + Cst b]) into two different cases.
   During the analysis of the two different cases,
   randoms must be used to encrpyt the same messages.
   This file defines systems for:
   - The same message on both sides (should be ok)
   - Different messages on both sides (should fail)
   Tests are performed for symmetric and assymetric encryption. *)

set securityTypes = true.

channel c
senc symenc,sdec
aenc asymenc,adec,pk
name k : message, SK[symenc, Low]
name sk : message, AK[asymenc, Low]
abstract a : message
abstract b : message
name r : message, Rand
mutable s : message, Cst a + Cst b = a.

axiom[any] cte : a <> b <: Real.z.
hint rewrite cte.

(* Uses [r] in two different encryptions, in two different branches induced by Break-Sum. *)
system sys1 = (out(c, <if s = a then symenc(a,r,k) else empty,
                       if s = a then empty else symenc(a,r,k)>)).
system sys2 = (out(c, <if s = a then symenc(a,r,k) else empty,
                       if s = a then empty else symenc(b,r,k)>)).
system sys3 = (out(c, <if s = a then asymenc(a,r,pk(sk)) else empty,
                       if s = a then empty else asymenc(a,r,pk(sk))>)).
system sys4 = (out(c, <if s = a then asymenc(a,r,pk(sk)) else empty,
                       if s = a then empty else asymenc(b,r,pk(sk))>)).


(* The tactic typing must succeed only in well-typed systems: [sys1] and [sys3].*)

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
  checkfail typing H exn Failure.
Abort.
lemma[sys3] _ : h=l => false.
Proof.
  intro H.
  typing H.
Qed.
lemma[sys4] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
