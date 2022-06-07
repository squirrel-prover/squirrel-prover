

channel c

system A:  in(c,x);out(c,x);
       A1: in(c,x);out(c,x).

equiv test : input@A1, frame@A.
Proof.
  nosimpl(fadup).
  nosimpl(admit 0).
  refl.
Qed.
