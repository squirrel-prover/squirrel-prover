include Basic.

channel c.

hash h.
name k : message.

abstract test : index -> boolean.
process A(i : index) =
  in(c,x);
  A: out(c,if test(i) then h(x,k)).

system !_i A(i).

global goal _ (j : index[const]) :
[(zero <> input@A(j)) = true] ->
[(forall (i:index), (A(i) < A(j) => test(i) => zero <> input@A(i))) = true] ->
[happens(A(j))] ->
equiv(frame@A(j), h(input@A(j),k)) ->
equiv(frame@A(j), h(zero,k)).
Proof. 
  intro H1 H2 Hap E. 
  rewrite /frame /exec /cond /output.
  fa 0.
  prf 2.
  rewrite H1 H2.
  rewrite if_true in 2; 1: auto.
  fresh 2; 1:auto.    
  apply E.
Qed.
