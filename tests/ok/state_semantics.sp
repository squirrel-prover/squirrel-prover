set processStrictAliasMode=true.

hash h

name key : index->message

mutable k1 : index->message
mutable k2 : index->message

channel c

process Tag(i:index,j:index) =
  k1(i) := h(k1(i),key(i));
  T: out(c, <k1(i),k2(i)>);

  k1(i) := h(k1(i),key(i));
  k2(i) := <k1(i),k2(i)>;
  T1: out(c,  <k1(i),k2(i)>);

  k1(i) := h(k1(i),key(i));
  let k3 = <k1(i),k2(i)> in
  T2: out(c, k3);

  let k4 = <k1(i),k2(i)> in
  k1(i) := h(k1(i),key(i));
  let k5 = <k1(i),k4> in
  T3: out(c, k5).

system (!_i !_j Tag(i,j)).

goal stateSemantics1:
  forall (i,j:index),
    output@T(i,j) = <h(k1(i)@pred(T(i,j)),key(i)),k2(i)@pred(T(i,j))>.
Proof.
nosimpl(intros).
simpl.
Qed.

goal stateSemantics2:
  forall (i,j:index),
    output@T1(i,j) =
      < h(k1(i)@pred(T1(i,j)),key(i)),
        <h(k1(i)@pred(T1(i,j)),key(i)),k2(i)@pred(T1(i,j))>>.
Proof.
nosimpl(intros).
simpl.
Qed.

goal stateSemantics3:
  forall (i,j:index), output@T2(i,j) = <h(k1(i)@pred(T2(i,j)),key(i)),k2(i)@pred(T2(i,j))>.
Proof.
nosimpl(intros).
simpl.
Qed.

goal stateSemantics4:
  forall (i,j:index), output@T3(i,j) = <h(k1(i)@pred(T3(i,j)),key(i)),<k1(i)@pred(T3(i,j)),k2(i)@pred(T3(i,j))>>.
Proof.
nosimpl(intros).
simpl.
Qed.
