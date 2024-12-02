include Core.

(* ------------------------------------------------------------- *)
channel c.

name k : message.
system P = C: out(c,k).

game G = {
  rnd k : message;
  oracle f = { return diff(k,empty); }
}.

global lemma [P] _ (t:timestamp[adv]) : 
  equiv(t, diff(k,empty)).
Proof.
  crypto G.
Qed.

axiom [P] foo (t:timestamp[adv]) : C <= t => false.

global lemma [P] _ (t:timestamp[adv]) : 
  Let u = frame@t in
  equiv(u,t, diff(k,empty)).
Proof.
  intro u. 
  crypto G. 
  apply foo.
Qed. 
