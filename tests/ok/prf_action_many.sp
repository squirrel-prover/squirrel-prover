include Basic.

(* Test that the prf tactic creates the correct formula when
 * several instances of the name are found in an action. 
 * Each time, the prf condition does not hold. We add it in hypothesis and check
 * that it has been correctly produced. *)
channel c
hash h
name k : message
name n : index->message
name m : index->message
system !_i !_j out(c,h(<n(i),n(j)>,k)).

(* only directy cases *)
global goal _ (i:index[param]) : 
[(diff(n(i),m(i)) <> <n(i),n(i)>) = true] ->
[happens(A(i,i))] -> 
equiv(output@A(i,i), h(diff(n(i),m(i)),k)).
Proof.
  intro H Hap.
  prf 1. 
  rewrite H.
  by rewrite if_true in 1. 
Qed.


(* This time with `frame`, which yields (only) indirect cases *)
global goal _ (i:index[param]) : 
[(diff(n(i),m(i)) <> <n(i),n(i)>) = true] ->
[(forall (i0,j:index),
  diff(
    A(i0,j) < A(i,i) => n(i) <> <n(i0),n(j)>,
    A(i0,j) < A(i,i) => m(i) <> <n(i0),n(j)>)
 ) = true] ->
equiv(frame@A(i,i)) ->
[happens(A(i,i))] -> 
equiv(frame@A(i,i), h(diff(n(i),m(i)),k)).
Proof.
  intro H1 H2 E Hap. 
  prf 1.
  rewrite H1 H2.
  rewrite if_true in 1; 1: auto.
  fresh 1; 1:auto.
  by apply E.
Qed.
