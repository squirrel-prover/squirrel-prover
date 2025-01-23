channel c.
abstract b : bool.

system null.

lemma rw (b0,b1:bool) (x,y:message) :
if diff(b0,b1) then x else y = 
diff(if b0 then x else y, if b1 then x else y).
Proof.
  by project.
Qed.


global lemma _ b0 b1 (x0, x1, y : message):
equiv(if diff(b0,b1) then diff(x0,x1) else y).
Proof.
  (* the proof-script below used to yield an anomaly 
     (see #270) *)
  rewrite rw.
  simpl.
Abort.
