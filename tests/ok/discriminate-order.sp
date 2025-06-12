include "Data/List.sp".

(*------------------------------------------------------------------*)
lemma _ @system:any (x : int) (l : list int) :
  l < Cons x l.
Proof. discriminate. Qed.

lemma _ @system:any (x : int) (l : list int) :
  l > Cons x l.
Proof. checkfail discriminate exn Failure. Abort.

lemma _ @system:any (x : int) (l : list int) :
  Cons x l < l.
Proof. checkfail discriminate exn Failure. Abort.

lemma _ @system:any (x : int) (l : list int) :
  Cons x l > l.
Proof. discriminate. Qed.

(*------------------------------------------------------------------*)
(* non-struct inequalities *)
lemma _ @system:any (x : int) (l : list int) :
  l <= Cons x l.
Proof. discriminate. Qed.

lemma _ @system:any (x : int) (l : list int) :
  l >= Cons x l.
Proof. checkfail discriminate exn Failure. Abort.

lemma _ @system:any (x : int) (l : list int) :
  Cons x l <= l.
Proof. checkfail discriminate exn Failure. Abort.

lemma _ @system:any (x : int) (l : list int) :
  Cons x l >= l.
Proof. discriminate. Qed.

(*------------------------------------------------------------------*)
(* depth 2 *)
lemma _ @system:any (x : int) (l : list int) :
  l < Cons x (Cons x l).
Proof. discriminate. Qed.

(*------------------------------------------------------------------*)
(* lexico with tuples *)
lemma _ @system:any (x : int) (l : list int) :
  (l,l) < (l,l).
Proof. checkfail discriminate exn Failure. Abort.

lemma _ @system:any (x : int) (l : list int) :
  (l,l) < (l,Cons x l).
Proof. discriminate. Qed.

lemma _ @system:any (x : int) (l : list int) :
  (l,l) < (Cons x l,l).
Proof. discriminate. Qed.

lemma _ @system:any (x : int) (l : list int) :
  (l,l) < (Cons x l,Cons x l).
Proof. discriminate. Qed.


lemma _ @system:any (x : int) (l : list int) :
  (l,Cons x l) < (l,l).
Proof. checkfail discriminate exn Failure. Abort.

lemma _ @system:any (x : int) (l : list int) :
  (l,Cons x l) < (l,Cons x l).
Proof. checkfail discriminate exn Failure. Abort.

lemma _ @system:any (x : int) (l : list int) :
  (l,Cons x l) < (Cons x l,l).
Proof. discriminate. Qed.

lemma _ @system:any (x : int) (l : list int) :
  (l,Cons x l) < (Cons x l,Cons x l).
Proof. discriminate. Qed.



lemma _ @system:any (x : int) (l : list int) :
  (Cons x l, l) < (l,l).
Proof. checkfail discriminate exn Failure. Abort.

lemma _ @system:any (x : int) (l : list int) :
  (Cons x l, l) < (l,Cons x l).
Proof. checkfail discriminate exn Failure. Abort.

lemma _ @system:any (x : int) (l : list int) :
  (Cons x l, l) < (Cons x l,l).
Proof. checkfail discriminate exn Failure. Abort.

lemma _ @system:any (x : int) (l : list int) :
  (Cons x l, l) < (Cons x l,Cons x l).
Proof. discriminate. Qed.


(*------------------------------------------------------------------*)
(* backward *)

lemma _ @system:any (x : int) (l : list int) :
  l < Cons x l => false.
Proof. intro H. checkfail discriminate H exn Failure. Abort.

lemma _ @system:any (x : int) (l : list int) :
  l > Cons x l => false.
Proof. intro H. discriminate H. Qed.

lemma _ @system:any (x : int) (l : list int) :
  Cons x l < l => false.
Proof. intro H. discriminate H. Qed.

lemma _ @system:any (x : int) (l : list int) :
  Cons x l > l => false.
Proof. intro H. checkfail discriminate H exn Failure. Abort.
