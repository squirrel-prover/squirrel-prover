name s0 : message.
mutable s : message = s0.
channel c.
system (A: out(c,of_bool(true)) | B: out(c,of_bool(false))).

name m : message.
equiv ax_ground : frame@pred(A),diff(s@B,m).
Proof.
  admit.
Qed.

goal [default/left] test_ground :
  input@A = s@B => False.
Proof.
  reach_equiv ax_ground.
  fresh Meq.
Qed.
