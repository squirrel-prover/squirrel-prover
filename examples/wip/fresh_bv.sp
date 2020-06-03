(* An example where we cannot conclude after using fresh *)

name n : index->index->message

channel c

system !_i if forall j:index, n(i,j)=n(i,j) then out(c,n(i,i)).

equiv test.
Proof.
  induction t.

  (* Then branch *)
  expandall. fa 0. fa 2.
  equivalent (forall j:index, n(i,j)=n(i,j)), True.
    split.
  (* Here we "forget" than the n(i,i) only occurs when exec@pred(A(i)). *)
  fa 2.
  fresh 2; yesif 2.
    split.
    (* For A(i1) we conclude immediatey: A(i1)<A(i) implies i1<>i.
       It is not immediate for A1(i1):
       if i1=i and A1(i1) < A(i) then we have two contradictory
       conditions in exec@A(i)... find a way to include exec@A(i)
       among hypotheses ? *)
    admit.
    (* Same problem on the right *)
    admit.

   (* Else branch *)
   expandall; fa 1; fa 2; fa 0.
   equivalent (forall j:index, n(i,j)=n(i,j)), True.
     split.
Qed.
