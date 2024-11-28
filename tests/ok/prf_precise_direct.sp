include Core.

channel c.

hash h.
name k : message.
name n: index -> message.

process A(i : index) =
  in(c,x);
  A: out(c,x).

system !_i A(i).

global lemma _ (j : index[param]) :
[forall (i:index), (A(i) < A(j) => zero <> n(i))] ->
 equiv(h(zero,k), seq(i:index => if A(i) < A(j) then h(n(i),k))).
Proof.
  intro H. 
  prf 0 => //.
Qed.
