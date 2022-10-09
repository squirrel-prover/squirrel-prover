

system null.

goal _ (i:index): i = i.
Proof.
 auto.
Qed.

goal _ (t:timestamp): t = t.
Proof.
 auto.
Qed.

goal _ (i:index,j:index): i=j => j=i.
Proof.
 auto.
Qed.

goal _ (i:index,j:index): i=j => not(j<>i).
Proof.
 auto.
Qed.

goal _ (x:timestamp,y:timestamp): x=y => y=x.
Proof.
 auto.
Qed.

goal _ (x:timestamp,y:timestamp): x<>y => y<>x.
Proof.
 auto.
Qed.

goal _ (x:timestamp,y:timestamp,z:timestamp):
  x=y => y=z => x<>z => False.
Proof.
 auto.
Qed.

goal _ (x:timestamp,y:timestamp,z:timestamp):
  y=z => x<>z => x<>y.
Proof.
 auto.
Qed.

goal _ (x:timestamp,y:timestamp,z:timestamp):
  y=z => x<>z => not(x=y).
Proof.
 auto.
Qed.

axiom eq_iff (x, y : boolean) : (x = y) = (x <=> y).

goal _ (t, t' : timestamp): (t <= pred(t')) = (t < t').
Proof. 
  by rewrite eq_iff. 
Qed.

(* `pred(init)` does not happens *)
goal _ : not (happens(pred(init))).
Proof. constraints. Qed.

(* surprisingly, if `pred(tau)` happens, then so does `tau` since
   `pred(_)` sends non-happening timestamps to non-happening 
   timestamps. *)
goal _ (tau : timestamp) : happens(pred(tau)) => happens(tau).
Proof. constraints. Qed.
