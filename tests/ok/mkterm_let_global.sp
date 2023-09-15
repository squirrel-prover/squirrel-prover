

channel c
system in(c,x);let y=x in out(c,x).

lemma _ (t:timestamp): y@t = y@t.
Proof.
 auto.
Qed.
