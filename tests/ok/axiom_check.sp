

(***************************************************************************
 *  Adding an axiom that clash with the existing signature axiomatization: *
 *  checksign(sign(x,y),pk(y)) -> true                                     *
 ***************************************************************************)

(* I have no idea what this was supposed to check.
   The signature axiomatization is now checksign(x, sign(x,y), pk(y)) -> true.
   It used to be checksign(sign(x,y), pk(y)) -> x.
   Originally here, mycheck said checksign(sign(x1,x2),pk(x2))=x1
   which was exactly the old axiom. *)

abstract ok : message

channel c

signature sign,checksign,pk 

system out(c,ok).

axiom mycheck (x1,x2: message): checksign(x1,sign(x1,x2),pk(x2))

axiom autre (x1:message): sign(x1,ok) = x1.

set timeout=1.

goal mygoal: False.

Proof.
 nosimpl(use mycheck with ok, ok).
 try congruence.
 (* this does not conclude, but should not timeout *)
 admit.
Qed.

