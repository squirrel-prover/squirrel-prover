(* This file tests the tactics `typing`.
   Indices must be constant for this tactic.
   This file defines systems with a non constant index in:
   - A function with a message argument
   - A function without message argument
   - A macros
   - A random for symetric encryption
   - A random for asymetric encryption
   It also tests the tactic in an empty system with:
   - a non constant index in a macro
   - a non constant timestamp in a macro*)

set securityTypes = true.

channel c
abstract mess_to_index : message -> index
abstract mess_to_timestamp : message -> timestamp
abstract id : index -> message
abstract f : index -> message -> message
mutable s(i:index) : message, Low = empty
senc symenc,sdec
aenc asymenc,adec,pk
name k : message, SK[symenc, Low]
name sk : message, AK[asymenc, Low]
name r : index -> message, Rand.

system sys1 = (in(c,x); out(c, id (mess_to_index x))).
system sys2 = (in(c,x); out(c, f (mess_to_index x) x)).
system sys3 = (in(c,x); s (mess_to_index x) := empty).
system sys4 = (!_i in(c,x); out(c, symenc(empty, r (mess_to_index x), k))).
system sys5 = (!_i in(c,x); out(c, asymenc(empty, r (mess_to_index x), pk(sk)))).
system sys = null.

name h : message, High
name l : message, Low.

lemma[sys1] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
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
  checkfail typing H exn Failure.
Abort.
lemma[sys] _ : forall x, h=s (mess_to_index x)@init => false.
Proof.
  intro x H.
  checkfail typing H exn Failure.
Abort.
global lemma[sys] _ : Forall (i : index[const]),
  [forall x, h=s i@(mess_to_timestamp x) => false].
Proof.
  intro i x.
  intro H.
  checkfail typing H exn Failure.
Abort.
