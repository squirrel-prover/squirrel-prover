system null.

goal forall (i:index), i = i.
Proof.
 simpl.
Qed.

goal forall (t:timestamp), t = t.
Proof.
 simpl.
Qed.

goal forall (i:index,j:index), i=j => j=i.
Proof.
 simpl.
Qed.

goal forall (i:index,j:index), i=j => not(j<>i).
Proof.
 simpl.
Qed.

goal forall (x:timestamp,y:timestamp), x=y => y=x.
Proof.
 simpl.
Qed.

goal forall (x:timestamp,y:timestamp), x<>y => y<>x.
Proof.
 simpl.
Qed.

goal forall (x:timestamp,y:timestamp,z:timestamp),
  x=y => y=z => x<>z => False.
Proof.
 simpl.
Qed.

goal forall (x:timestamp,y:timestamp,z:timestamp),
  y=z => x<>z => x<>y.
Proof.
 simpl.
Qed.

goal forall (x:timestamp,y:timestamp,z:timestamp),
  y=z => x<>z => not(x=y).
Proof.
 simpl.
Qed.
