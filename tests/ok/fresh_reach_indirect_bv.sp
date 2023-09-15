hash h
name k : message

name n : index * index -> message

channel c

system !_i
  if (exists (i':index), n(i',i') = n(i',i'))
  then out(c,n(i,i))
  else out(c,n(i,i)).

lemma test (i,j:index):
  i <> j =>
  h(fst(output@A(i)),k) <> n(i,j).

Proof.
 intro Hneq Heq.
 fresh Heq => [] _; auto.
Qed.
