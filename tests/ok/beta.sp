type T.

(*------------------------------------------------------------------*)
goal [any] _ (x : T): (fun (y : T) => y) x = x.
Proof. auto. Qed.

goal [any] _ (x, z : T): (fun (y : T) => z) x = z.
Proof. auto. Qed.

goal [any] _ (x : T): (fun (y : T) => (x,y)) x = (x,x).
Proof. auto. Qed.

(*------------------------------------------------------------------*)
abstract a : T.

op g : T = (fun (y : T) => y) a.

(*------------------------------------------------------------------*)
op f : T -> T = fun (x : T) => x.

goal [any] _ (x : T): f x = x.
Proof. auto. Qed.

(*------------------------------------------------------------------*)
op f2 : T -> T -> T = fun (x,y : T) => x.

(*------------------------------------------------------------------*)
(* eta-equivalence *)

goal [any] _ (z1,z2 : T): (fun (x : T) => f2 x) = f2.
Proof. auto. Qed.

goal [any] _ (z1,z2 : T): (fun (x,y : T) => f2 x y) = f2.
Proof. auto. Qed.

goal [any] _ (z1,z2 : T): (fun (x,y : T) => f2 y x) = f2.
Proof. checkfail auto exn GoalNotClosed. Abort. 

(*------------------------------------------------------------------*)
(* some applications *)

goal [any] _ (z1,z2 : T): (fun (x : T) => f2 z1 x) z2 = z1.
Proof. auto. Qed.

goal [any] _ (z1,z2 : T): (fun (x : T) => fun (y : T) => f2 y x) z2 z1 = z1.
Proof. auto. Qed.

goal [any] _ (z1,z2 : T): f2 z1 z2 = z1.
Proof. auto. Qed.

goal [any] _ (z1,z2 : T): f2 z1 z1 = z1.
Proof. auto. Qed.

goal [any] _ (z1,z2 : T): (f2 z1) z2 = z1.
Proof. auto. Qed.

(* same goal, with forced unfolding  *)
goal [any] _ (z1,z2 : T): (f2 z1) z2 = z1.
Proof. rewrite /f2. auto. Qed.

(*------------------------------------------------------------------*)
op g2 ['a] (x,y: 'a) : 'a = x.

goal [any] _ (z1,z2 : T): g2 z1 z2 = z1.
Proof. auto. Qed.

(*------------------------------------------------------------------*)
op h2 ['a] (x : 'a) : 'a -> 'a = fun (y : 'a) => x.

goal [any] _ (z1,z2 : T): h2 z1 z1 = h2 z1 z2.
Proof. auto. Qed.

(*------------------------------------------------------------------*)
op k2 ['a] : 'a -> 'a -> 'a = fun (x,y : 'a) => x.

(* For now, expanding `k2` fails because `k2` contains 
   free type variables, which cannot be inferred during its unfolding.
   Could be fixed with a better type system. *)
goal [any] _ (z1,z2 : T): k2 z1 = k2 z2.
Proof. 
  checkfail auto exn GoalNotClosed.
Abort.

