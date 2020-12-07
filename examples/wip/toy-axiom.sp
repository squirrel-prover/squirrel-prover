(*******************************************************************************
Toy example de Stephanie
*******************************************************************************)
abstract ok : message


channel c

signature sign,checksign,pk 

axiom mycheck : forall (x1,x2: message), checksign(sign(x1,x2),pk(x2)) = x1

axiom autre: forall (x1:message), sign(x1,ok) = x1



system out(c,ok).


goal mygoal: False.

Proof.
 apply autre to ok.
 admit.
Qed.


goal othergoal: False.

Proof.
 apply mycheck to ok, ok.
 (* squirrel part dans les choux *)
Qed.
