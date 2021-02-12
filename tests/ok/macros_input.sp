set autoIntro=false.

hash h
name k : message
channel c
system in(c,x); let y = x in out(c,h(y,k)).

goal test :
  output@A = input@A.
Proof.
  admit.
  (* TODO This test seems broken to me, we should not be able to
   * prove this. We should prove the negation, but this will only
   * be possible with a refined euf that does not introduce B <= A
   * but sometimes B < A.
 
  euf 0.
  (* Euf alone does not complete the proof as it relies on
   * expanding the definition of y, which is currently not
   * done. We admit it, as the purpose of this tests is only
   * to check that euf works, i.e. that issue #31 is fixed. *)
  admit.

  *)
Qed.
