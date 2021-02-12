set autoIntro=false.

(* Checking the treatment of bound variables in indirect cases for xor. *)

name n : index->message
name m : index->message

abstract ok : message
abstract ko : message

channel c

system !_i out(c,<n(i),seq(i->n(i))>).


axiom len_ok : forall i:index, len(ok) = len(n(i))
axiom len_ko : forall i:index, len(ko XOR m(i)) = len(n(i))
axiom len_ko_ok : forall i:index, len(ko XOR ok) = len(n(i)).

(* The main test, with a non-empty list of bound variables. *)
equiv nonempty (tau:timestamp,i:index) : output@tau, n(i) XOR diff(ok,m(i)).
Proof.  
  xor 1.
  (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  equivalent
    (forall (i1,i2:index) A(i1)<=tau => i2 <> i && i1<>i),
    True.
  admit.
  nosimpl(yesif 1). 
  by namelength n(i),m(i); apply len_ok to i; auto.

  fa 1.
  admit. (* Ignore final equivalence goal. *)
Qed.

(* The same test, but giving the fresh name as argument to the xor tactic. *)
equiv nonempty2 (tau:timestamp,i:index) :
  output@tau, ko XOR diff(ok,m(i)) XOR n(i).
Proof.
  xor 1, n(i).
  (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  equivalent
    (forall (i1,i2:index) A(i1)<=tau => i2 <> i && i1<>i),
    True.
  admit.
  nosimpl(yesif 1).
  by apply len_ko_ok to i; apply len_ko to i.
  fa 1.
  admit. (* Ignore final equivalence goal. *)
Qed.
