op m1 : message.
channel c.
process A =
   out(c, m1).
system sys = !_i A. 

global lemma [sys] _ (i:_):
   [witness = output@A i] 
     -> [happens(A i) =>  m1 = witness].
Proof.
intro H1. intro H. 
checkfail rewrite /output in H1 exn Failure.
Abort.
