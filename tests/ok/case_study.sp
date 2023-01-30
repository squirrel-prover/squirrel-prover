include Basic.

channel c.

hash h.
name k : message.
name n: index -> message.

process A(i : index) =
  in(c,x);
  A: out(c,x).

system !_i A(i).

global goal _ (b : boolean, x,y : message) :
 equiv(if x<y then x else y, if not (x<y) then y else x).
Proof.
 cs (x<_) 0.
Qed.

