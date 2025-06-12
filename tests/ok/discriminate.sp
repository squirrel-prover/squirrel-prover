include "Data/List.sp".

(*------------------------------------------------------------------*)
lemma _ @system:any (x,x' : int) (l,l' : list int) :
  Cons x' l' = Cons x l => false.
Proof. intro H. checkfail discriminate H exn Failure. Abort.

lemma _ @system:any (x : int) (l : list int) :
  Cons x l = Nil => false.
Proof. intro H. discriminate H. Qed.

lemma _ @system:any (x,x' : int) (l,l' : list int) :
  Nil = Cons x l => false.
Proof. intro H. discriminate H. Qed.

lemma _ @system:any :
  Nil[int] = Nil => false.
Proof. nosimpl intro H. checkfail discriminate H exn Failure. Abort.
