include Basic.

action A : 1.

channel c.
abstract one : message.

process B (i : index) = A: out(c, if exists (j : index), A(j) < A(i) then one else zero).

system !_i B(i).

goal _ (i, j : index) : A(i) < A(j) => output@A(j) = one.
Proof.
  intro Hap. 
  rewrite /output if_true //; 1: by exists i.
Qed.
