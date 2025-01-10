channel c.

system P = null.

axiom eqdiff @system:P (x:message) : x = diff(x,x).

(* check that lemma application correcly handles nested diffs *)
lemma _ 
  @system:P
   (u,v,w : message) 
:
  true.
Proof. 
  nosimpl have ? := eqdiff (diff(u,v)). 
  simpl. 
Abort.
