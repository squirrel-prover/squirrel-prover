channel c


system A: in(c,x);out(c,x);
       B: in(c,y);out(c,diff(x,y)).

axiom [test] triv_false : False.



goal [left] test_left_bis : False.
Proof.
  apply triv_false.
Qed.
