hash h
channel c

name k : message

name ok : message


system
!_i (out(c,h(ok,k))| in(c,x);if x=h(zero,k) then out(c,diff(ok,zero))).




 equiv [left] [right] simp.
 Proof.
 case t.


 expand frame@A1(i).
 expand output@A1(i).
fa 0.
 noif 1.

 expand exec@A1(i).
expand cond@A1(i).
introsleft H1.euf M0.

fa 1.
induc.

cycle 1.

 expand frame@A(i).
 expand output@A(i).
expand exec@A(i).
expand cond@A(i).

(* To prove this goal, one will need to be able to enrich the induction to
hypothesis with h(ok,k),frame@pred(A(i). *)
