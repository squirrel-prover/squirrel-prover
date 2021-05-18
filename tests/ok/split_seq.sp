set autoIntro=false.

abstract ok : index->message
channel c

(*------------------------------------------------------------------*)
system A: !_i in(c,x);out(c,<ok(i),x>).

equiv _ (t : timestamp) (j:index) : 
seq(i->(if (A(i) <= A(j) && A(i) <> t) then <ok(i),input@A(i)>)),
seq(i->(if not((A(i) <= A(j) && A(i) <> t)) then <ok(i),input@A(i)>))
->
seq (i -> <ok(i), input@A(i)>).
Proof.
  intro H.
  nosimpl(splitseq 0: (fun (l:index) -> A(l) <= A(j) && A(l) <> t)).
  auto.
Qed.  

(* same but using the same binded name in splitseq *)
equiv _ (t : timestamp) (j:index) : 
seq(i->(if (A(i) <= A(j) && A(i) <> t) then <ok(i),input@A(i)>)),
seq(i->(if not((A(i) <= A(j) && A(i) <> t)) then <ok(i),input@A(i)>))
->
seq (i -> <ok(i), input@A(i)>).
Proof.
  intro H.
  nosimpl(splitseq 0: (fun (i:index) -> A(i) <= A(j) && A(i) <> t)).
  auto.
Qed.  

(* same, but with a seq using a variable name which is also free in the sequent *)
equiv _ (t : timestamp) (i:index) : 
seq(i0->(if (A(i0) <= A(i) && A(i0) <> t) then <ok(i0),input@A(i0)>)),
seq(i0->(if not((A(i0) <= A(i) && A(i0) <> t)) then <ok(i0),input@A(i0)>))
->
seq (i -> <ok(i), input@A(i)>).
Proof.
  intro H.
  nosimpl(splitseq 0: (fun (l:index) -> A(l) <= A(i) && A(l) <> t)).
  auto.
Qed.  
