lemma [any] _ (x,y : message) : (x, y)#1 = x.
Proof.
  auto. 
Qed.

lemma [any] _ (x,y : message) : (x, y)#2 = y.
Proof.
  auto. 
Qed.

(*------------------------------------------------------------------*)
(* same, with types T,T' *)

type T.
type T'.

lemma [any] _ (x : T, y : T') : (x, y)#1 = x.
Proof.
  auto. 
Qed.

lemma [any] _ (x : T, y : T') : (x, y)#2 = y.
Proof.
  auto. 
Qed.

(*------------------------------------------------------------------*)
type T''.

lemma [any] _ (x : T, y : T', z : T'') : (x, y,z)#3 = z.
Proof.
  auto. 
Qed.

lemma [any] _ (x : T, y : T', z : bool) : z => (x, y,z)#3.
Proof.
  auto. 
Qed.


(*------------------------------------------------------------------*)

(* typer sanity check *)
lemma [any] _ (x : T * T) : x#1 = x#2.
Proof. Abort. 

(* typer sanity check *)
lemma [any] _ (x,y : T * T') : x#1 = y#1.
Proof. Abort. 

