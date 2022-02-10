set autoIntro=false.

(* Check `assert (ip := pt)` tactic *)

name k:message

system null.

axiom axiom1 (ma : message): exists (m:message), k = m && m = ma.

goal _ (ma : message) : ma = k.
Proof.
 assert (H := axiom1 ma). 
 destruct H as [m [H1 H2]].
 rewrite -H2 -H1.
 clear H1 H2.
 congruence.
Qed.

(* with an intro pattern *)
goal _ (ma : message) : ma = k.
Proof.
 assert ([m [H1 H2]] := axiom1 ma). 
 rewrite -H2 -H1.
 clear H1 H2.
 congruence.
Qed.

(*------------------------------------------------------------------*)
axiom axiom2 (ma : message): ma = k => k = ma.

(* check that implications are not introduced by default *)
goal _ (ma : message) : ma = k => k = ma.
Proof.
 intro Hyp.
 assert (H := axiom2 ma). 
 apply H.
 assumption.
Qed.
