(* This file tests the tactics `typing`.
   This file check public keys for asymetric encryption and
   signature verification. *)

set securityTypes = true.

channel c
aenc enc,dec,pk
signature sign,ver,vk
name k : message, AK[enc, Low]
name r : message, Rand
abstract a : message
abstract b : message
name signk : message, SSK[sign, Cst a].

name h : message, High
name l : message, Low.

system sys1 = (in(c, x); out(c,enc(empty,r,pk(k)))).
system sys2 = (in(c, x); out(c,enc(empty,r,k))).
system sys3 = (in(c, x); out(c,if ver(fst x, snd x, vk(signk)) then if snd x = b then h)). (*Forces the use of the rule Ver*)
Proof. admit. Qed.
system sys4 = (in(c, x); out(c,if ver(fst x, snd x, signk) then if fst x = b then h)).

(* The tactic typing must succeed only in well-typed systems:
   [sys1] and [sys3].*)

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
