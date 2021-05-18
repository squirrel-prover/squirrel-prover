set autoIntro=false.

abstract ok : index->message
channel c

(*------------------------------------------------------------------*)
system A: !_i in(c,x);out(c,<ok(i),x>).

axiom if_true (x,y : message): if true then x else y = x.

axiom if_false  (x,y : message): if false then x else y = y.

(*------------------------------------------------------------------*)
equiv _ (x : message): 
[forall (i : index), ok(i) = x] ->
seq (i -> diff(ok(i), x)).
Proof.
  intro H.
  constseq 0: x. 
  by project. 
  refl.
Qed.  

abstract even : index -> boolean.

equiv _ (x,y : message): 
[forall (i : index), even(i) => ok(i) = x] ->
[forall (i : index), not (even(i)) => ok(i) = y] ->
seq (i -> diff(ok(i), if even(i) then x else y)).
Proof.
  intro HE HO.
  constseq 0: x y; 2: auto.
  intro i.
  project.
  case (even (i)) => He. 
  by left; apply HE.
  by right; apply HO.

  case even(i). 
  by rewrite if_true. 
  by rewrite !if_false.
Qed.  
