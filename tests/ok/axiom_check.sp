(***************************************************************************
 *  Adding an axiom that clash with the existing signature axiomatization: *
 *  checksign(sign(x,y),pk(y)) -> true                                     *
 ***************************************************************************)

abstract ok : message

channel c

signature sign,checksign,pk 

axiom mycheck : forall (x1,x2: message), checksign(sign(x1,x2),pk(x2)) = x1

axiom autre: forall (x1:message), sign(x1,ok) = x1

system out(c,ok).

set timeout=1.

goal mygoal: False.

Proof.
 nosimpl(apply mycheck to ok, ok).
 try congruence.
 (* this does not conclude, but should not timeout *)
 admit.
Qed.

