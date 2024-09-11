channel c
abstract f : message->message
abstract ff : message->message

system P =
  !_i
  in(c,x);
  let a = f(x) in
  let b = ff(a) in
  A: out(c,b).

lemma [P] _ (i:index): happens(A(i)) => output@A(i) = ff(f(input@A(i))).
Proof.
  intro H.
  rewrite /output. rewrite /b. rewrite /a.
  auto.
Qed.

(* ----------------------------------------------------------------------------- *)
mutable s1 = empty.
mutable s2 = empty.

system Q =
  !_i
  in(c,x);
  s1 := x;
  let a1 = f(<x,s1>) in
  s2 := <a1,x>;
  let b1 = ff(<a1,<s1,s2>>) in
  A: out(c,b1).

lemma [Q] _ (i:index): 
  happens(A(i)) => 
  output@A(i) = 
    ff(< f(<input@A i,s1@A i>), 
        <s1@A i, 
         s2@A i>>).
Proof.
  intro H.
  rewrite /output. rewrite /b1. rewrite /a1.
  auto.
Qed.
