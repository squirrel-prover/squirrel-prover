(* test apply argument inference *)
set autoIntro=false.

system null.

abstract nt ['a] : 'a -> 'a.
abstract ft ['a] : 'a -> 'a -> 'a.
abstract gt ['a] : 'a -> 'a -> boolean.


goal _ (x, y : message) : 
    (forall (z : message), gt(nt(x),z) => false ) => 
    gt(nt(x),nt(y)) => 
    false.
Proof.
  intro H A.
  by assert (G := H _ (:: A)).
Qed.


goal _ ['a] (x, y : 'a) : 
    (forall (z : 'a), gt(nt(x),z) => false ) => 
    gt(nt(x),nt(y)) => 
    false.
Proof.
  intro H A.
  by assert (G := H _ (:: A)).
Qed.


goal _ ['a] (x, y : 'a) : 
    (forall (z : 'a), gt(nt(x),z) => false ) => 
    gt(nt(y),nt(y)) => 
    false.
Proof.
  intro H A.
  checkfail by try assert (G := H _ (:: A)) exn GoalNotClosed.
Abort.
