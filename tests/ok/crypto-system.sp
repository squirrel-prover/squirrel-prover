(* test that `crypto` behaves correctly on manually-provided system
   expressions *)

 channel c hash h name s : message name k : message.

(* Preimage resistance *)
game PIR = {
  rnd k : message;
  rnd goal : message;
  oracle get_h x = { return h(x,k) }
  oracle get_goal = { return goal }
  oracle challenge x = { return diff(h(x,k) = goal, false) }
}.

system C2 = null.

global lemma [C2] toto :
  equiv (diff(h (zero, k) = s, false)).
Proof.
  crypto PIR (k: k) (goal: s).
Qed.

global lemma [set:C2/left; equiv:C2/left,C2/left] toto2 :
  equiv (diff(h (zero, k) = s, false)).
Proof.
  crypto PIR (k: k) (goal: s).
Qed.
