type int.

goal [any] _ (x : message) : (fun (y : int) => x) = (fun (z : int) => x).
Proof.
  auto.
Qed.


goal [any] _ (x, x' : message) :
  (fun (y : int) => x) = (fun (z : int) => x').
Proof.
  checkfail auto exn GoalNotClosed.
Abort.


goal [any] _ (x, x' : message) :
  x = x' =>
  (fun (y : int) => x) = (fun (z : int) => x').
Proof. by intro ->. Qed.

(*------------------------------------------------------------------*)
abstract nt ['a] : 'a -> 'a.
abstract gt ['a] : 'a * 'a -> bool.
abstract gtCurry ['a] : 'a -> 'a -> bool.

axiom [any] _ (x : message) : nt(x) = x. 
axiom [any] _ (x : message) : (x, nt(x)) = (nt(x), x). 
axiom [any] _ (x : message) : (x, nt x) = (nt x, x). 
axiom [any] _ (x : message) : gtCurry x x.
axiom [any] _ (x : message) : gtCurry (nt x) (nt x).
axiom [any] _ (x : message) : gt (x, x).

(*------------------------------------------------------------------*)
op foo ['a] (x : 'a) : 'a -> bool = gtCurry x.

goal [any] _ ['a] (x : 'a) : gtCurry x x => foo x x. 
Proof. auto. Qed.

(*------------------------------------------------------------------*)
type T.

goal [any] _ (x : T): (fun (y : T) => y) x = (fun (y : T) => y) x.
Proof. auto. Qed.

goal [any] _ (x, z : T): (fun (y : T) => y) x = (fun (y : T) => z) x.
Proof. checkfail auto exn GoalNotClosed. Abort. 

axiom [any] _ ['a 'b] (f : 'a -> 'b) (x,y : 'a) : x = y => f x = f y.
