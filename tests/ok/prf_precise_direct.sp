include Basic.

channel c.

hash h.
name k : message.
name n: index -> message.

process A(i : index) =
  in(c,x);
  A: out(c,x).

system !_i A(i).

global goal _ (j : index[param]) :
[forall (i:index), (A(i) < A(j) => zero <> n(i))] ->
 equiv(h(zero,k), seq(i:index => if A(i) < A(j) then h(n(i),k))).
Proof.
  intro H. 
  prf 0.
  rewrite if_true in 0 => //=.
  by intro i H1; fresh H1.
Qed.
