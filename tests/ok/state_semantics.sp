set processStrictAliasMode=true.

hash h.

name key : index -> message.

mutable k1(i:index): message = empty.
mutable k2(i:index): message = empty.

channel c.

mutex l : 0.

process Tag(i:index,j:index) =
  lock l;
  k1(i) := h(k1(i),key(i));
  T: out(c, <k1(i),k2(i)>);
  unlock l;

  lock l;
  k1(i) := h(k1(i),key(i));
  k2(i) := <k1(i),k2(i)>;
  T1: out(c,  <k1(i),k2(i)>);
  unlock l;

  lock l;
  k1(i) := h(k1(i),key(i));
  let k3 = <k1(i),k2(i)> in
  T2: out(c, k3);
  unlock l;

  lock l;
  let k4 = <k1(i),k2(i)> in
  k1(i) := h(k1(i),key(i));
  let k5 = <k1(i),k4> in
  T3: out(c, k5);
  unlock l.

system (!_i !_j Tag(i,j)).

lemma stateSemantics1 (i,j:index):
    happens(T(i,j)) => 
    output@T(i,j) = <h(k1(i)@pred(T(i,j)),key(i)),k2(i)@pred(T(i,j))>.
Proof. 
  intro Hap. 
  rewrite /output.
  auto.
Qed.


(* wrong timestamp happening *)
lemma stateSemantics1F (i,j:index):
    happens(T1(i,j)) => 
    output@T(i,j) = <h(k1(i)@pred(T(i,j)),key(i)),k2(i)@pred(T(i,j))>.
Proof.
  intro *. 
  depends T(i,j), T1(i,j) by assumption. 
  auto.
Qed.

lemma stateSemantics (i,j:index):
    happens(T1(i,j)) =>
    output@T1(i,j) =
      < h(k1(i)@pred(T1(i,j)),key(i)),
        <h(k1(i)@pred(T1(i,j)),key(i)),k2(i)@pred(T1(i,j))>>.
Proof. 
auto.
Qed.

lemma stateSemantics3 (i,j:index):
  happens(T2(i,j)) => 
  output@T2(i,j) = 
  <h(k1(i)@pred(T2(i,j)),key(i)),k2(i)@pred(T2(i,j))>.
Proof. 
auto.
Qed.

lemma stateSemantics4 (i,j:index):
  happens(T3(i,j)) => 
  output@T3(i,j) = <h(k1(i)@pred(T3(i,j)),key(i)),<k1(i)@pred(T3(i,j)),k2(i)@pred(T3(i,j))>>.
Proof.
auto.
Qed.
