system null.

include Basic.

name n  : index     -> timestamp.
name n1 : timestamp -> timestamp.
(* name n2 : message -> timestamp. *)

lemma _ (tau,tau' : timestamp) : n1(tau) = n1(tau') => tau = tau'.
Proof. 
  intro H. 
  checkfail auto exn GoalNotClosed.
Abort.

name m  : timestamp -> message.
name m1 : timestamp -> message.

lemma _ (tau,tau' : timestamp) : m1(tau) = m1(tau') => tau = tau'.
Proof. 
  intro H. 
  fresh H => ->. 
  apply eq_refl.
Qed.


lemma _ (tau : timestamp) : m(tau) = m1(tau) => false.
Proof. 
  intro H. 
  fresh H => U. 
Qed.
