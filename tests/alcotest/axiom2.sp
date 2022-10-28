channel c.

system A: in(c,x);out(c,x);
       B: in(c,y);out(c,diff(x,y)).

system [test] null.
axiom [test] triv_false : False.

goal [default/left] test_left_bis : False.
Proof.
  use triv_false.
Qed.
