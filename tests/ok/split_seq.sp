

abstract ok : index->message
channel c

(*------------------------------------------------------------------*)
system A: !_i in(c,x);out(c,<ok(i),x>).

global goal _ (t : timestamp) (j:index) :
  equiv(
    seq(i:index => (if (A(i) <= A(j) && A(i) <> t) then <ok(i),input@A(i)>)),
    seq(i:index => (if not((A(i) <= A(j) && A(i) <> t)) then <ok(i),input@A(i)>))) ->
  equiv(seq (i:index => <ok(i), input@A(i)>)).
Proof.
  intro H.
  nosimpl(splitseq 0: (fun (l:index) => A(l) <= A(j) && A(l) <> t)).
  auto.
Qed.

(* same but using the same binded name in splitseq *)
global goal _ (t : timestamp) (j:index) :
  equiv(
    seq(i:index =>(if (A(i) <= A(j) && A(i) <> t) then <ok(i),input@A(i)>)),
  	seq(i:index =>(if not((A(i) <= A(j) && A(i) <> t)) then <ok(i),input@A(i)>))) ->
  equiv(seq (i:index => <ok(i), input@A(i)>)).
Proof.
  intro H.
  nosimpl(splitseq 0: (fun (i:index) => A(i) <= A(j) && A(i) <> t)).
  auto.
Qed.

(* same, but with a seq using a variable name which is also free in the sequent *)
global goal _ (t : timestamp) (i:index) :
  equiv(
    seq(i0:index =>(if (A(i0) <= A(i) && A(i0) <> t) then <ok(i0),input@A(i0)>)),
  	seq(i0:index =>(if not((A(i0) <= A(i) && A(i0) <> t)) then <ok(i0),input@A(i0)>))
  ) ->
  equiv(seq (i:index => <ok(i), input@A(i)>)).
Proof.
  intro H.
  nosimpl(splitseq 0: (fun (l:index) => A(l) <= A(i) && A(l) <> t)).
  auto.
Qed.
