(* This file tests the tactics `typing`.
   Typing cannot consider the use of randoms in some locations.
   This file defines systems for:
   - A random used in the output (should be ok)
   - A random used in the mutable (should be ok)
   - A random used in the condition (should fail)
   - A random used in the hypothesis the tactic is used on (should fail)
   Tests are performed for symmetric and assymetric encryption. *)

set securityTypes = true.

channel c
senc symenc,sdec
aenc asymenc,adec,pk
name k : message, SK[symenc, Low]
name sk : message, AK[asymenc, Low]
abstract a : message
name r : message, Rand
mutable s : message, Low = a.

(* Uses [r] in two different encryptions, in two different branches induced by Break-Sum. *)
system sys1 = (out(c, symenc(a,r,k))).
system sys2 = (s := symenc(a,r,k); out(c, empty)).
system sys3 = (if symenc(a,r,k) = zero then out (c,empty)).
(* Empty system to test randoms in the hypothesis only. *)
system sys4 = null.
system sys5 = (out(c, asymenc(a,r,pk(sk)))).
system sys6 = (s := asymenc(a,r,pk(sk)); out(c, empty)).
system sys7 = (if asymenc(a,r,pk(sk)) = zero then out (c,empty)).
(* Empty system to test randoms in the hypothesis only. *)
system sys8 = null.

(* ------------------------------------------- *)
(* --- Simple lemma for the automatic test --- *)
(* ------------------------------------------- *)

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
lemma[sys4] _ : h=symenc(a,r,k) => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys5] _ : h=l => false.
Proof.
  intro H.
  typing H.
Qed.
lemma[sys6] _ : h=l => false.
Proof.
  intro H.
  typing H.
Qed.
lemma[sys7] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys8] _ : h=asymenc(a,r,pk(sk)) => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
