hash h

name kP : message
channel cP
channel cS

name a : index -> message
name b : index -> message

process P(i:index) =
  out(cP, a(i));
  in(cP, t);
   let sS = t in
  if sS = a(i) then
  out(cP, h(sS,kP))


process S(i:index) =
  A: in(cS, sP)

system (!_i P(i) | !_j S(j)).


(* Show that condition S1 implies the next one. *)
goal S1_charac :
forall (r:index),
  sS(r)@P1(r) = a(r).
Proof.
  simpl.
 admit.
Qed.


goal S1_charac :
forall (r:index),
  input@A(r) <> h(b(r),kP).
Proof.
  simpl.
  euf M0.
Qed.
