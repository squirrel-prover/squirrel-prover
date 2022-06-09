

channel c

system A:  in(c,x);out(c,x);
       A1: in(c,x);out(c,x).

(* This is allowed as input@A = g(frame@pred(A)). *)
equiv test_pred : input@A, frame@pred(A).
Proof.
  nosimpl(fadup).
  nosimpl(admit 0).
  refl.
Qed.
equiv test_pred_t (t:timestamp) : input@t, frame@pred(t).
Proof.
  nosimpl(fadup).
  nosimpl(admit 0).
  refl.
Qed.

(* Same as before, using additionnally frame@pred(t) = fst(frame@t). *)
equiv test (t:timestamp) : input@t, frame@t.
Proof.
  nosimpl(fadup).
  nosimpl(admit 0).
  refl.
Qed.

(* Same as above, because A1 must occur after A. *)
equiv test_depends : input@A, frame@A1.
Proof.
  nosimpl(fadup).
  nosimpl(admit 0).
  refl.
Qed.
