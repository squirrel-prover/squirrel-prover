set autoIntro=false.

system null.

goal _ (i:index): i = i.
Proof.
 by auto.
Qed.

goal _ (t:timestamp): t = t.
Proof.
 by auto.
Qed.

goal _ (i:index,j:index): i=j => j=i.
Proof.
 by auto.
Qed.

goal _ (i:index,j:index): i=j => not(j<>i).
Proof.
 by auto.
Qed.

goal _ (x:timestamp,y:timestamp): x=y => y=x.
Proof.
 by auto.
Qed.

goal _ (x:timestamp,y:timestamp): x<>y => y<>x.
Proof.
 by auto.
Qed.

goal _ (x:timestamp,y:timestamp,z:timestamp):
  x=y => y=z => x<>z => False.
Proof.
 by auto.
Qed.

goal _ (x:timestamp,y:timestamp,z:timestamp):
  y=z => x<>z => x<>y.
Proof.
 by auto.
Qed.

goal _ (x:timestamp,y:timestamp,z:timestamp):
  y=z => x<>z => not(x=y).
Proof.
 by auto.
Qed.
