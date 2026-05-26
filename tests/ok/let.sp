(* Test macros associated to let definition,
 * even when they are used in subsequent actions. *)

channel c

abstract ok : message
abstract ko : message

system S:
  !_i in(c,x);
      let def = <x,x> in
      out(c,x);
      try find j such that def=def in
        out(c,ok)
      else
        out(c,ko).

lemma def_S : 
  forall (i:index),
  happens(S(i)) => def@S(i) = <input@S(i),input@S(i)>.
Proof.
  auto.
Qed.

lemma def_S1 : 
  forall (i,j:index),
  happens(S1(i,j)) =>  def@S1(i,j) = <input@S(i),input@S(i)>.
Proof. 
  auto.
Qed.

lemma def_S2 : 
  forall (i:index),
  happens(S2(i)) => def@S2(i) = <input@S(i),input@S(i)>.
Proof.
  auto.
Qed.

system Snest = 
(  !_i !_j in(c,x);
      let def2 = x  in
      out(c,x);
      !_k out(c,def2)) | out(c,empty). 

lemma [Snest] _ : 
  forall (i,j,k:index),
  happens(A(i,j),A1(i,j,k)) => def2@A(i,j) = def2@A1(i,j,k).
Proof.
 intro i j k Hap.
 by rewrite /def2.
Qed.


lemma [Snest] _ : 
  happens(A2) => def2@A2 = empty.
Proof.
 intro Hap.
 checkfail rewrite /def exn Failure.
Abort.
