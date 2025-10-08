(* This file tests the tactics `typing`.
   If a system uses a random for encryption in an action,
   it must uses exactly the same indices as the action.
   This file defines systems for:
   - A random r2[i,j] in A[i,j] (should be ok)
   - A random r2[j,i] in A[i,j] (should fail)
   - A random r1[i] in A[i,j]   (should fail)
   - A random r0 in A[i,j]v     (should fail)
   Tests are performed for symmetric and assymetric encryption. *)

set securityTypes = true.

channel c
senc symenc,sdec
aenc asymenc,adec,pk
abstract m : message.
name k : message, SK[symenc, Low]
name sk : message, AK[asymenc, Low]
name r2 : index * index -> message, Rand
name r1 : index -> message, Rand
name r0 : message, Rand.

system sys1 = (!_i !_j A: out(c,symenc(m,r2(i,j),k))).
system sys2 = (!_i !_j A: out(c,symenc(m,r2(j,i),k))).
system sys3 = (!_i !_j A: out(c,symenc(m,r1(i),k))).
system sys4 = (!_i !_j A: out(c,symenc(m,r0,k))).
system sys5 = (!_i !_j A: out(c,asymenc(m,r2(i,j),pk(sk)))).
system sys6 = (!_i !_j A: out(c,asymenc(m,r2(j,i),pk(sk)))).
system sys7 = (!_i !_j A: out(c,asymenc(m,r1(i),pk(sk)))).
system sys8 = (!_i !_j A: out(c,asymenc(m,r0,pk(sk)))).

(* The tactic typing must succeed only in well-typed systems: [sys1] and [sys5].*)

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
  typing H.
Qed.
lemma[sys6] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys7] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys8] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
