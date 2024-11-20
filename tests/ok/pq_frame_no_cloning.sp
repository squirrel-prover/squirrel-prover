include Core.
open Quantum.
close Classic.

channel c.

op f : message -> message.

system [postquantum] P = !_i in(c,x); A: out(c, f x).

(* the previous `transcripts` can be computed from a latter transcripts *)
global lemma [P] _ (t, t' : _[adv]) :
  [t' < t] -> equiv(transcript@t) -> equiv(transcript@t').
Proof.
  intro A E.
  apply E.
Qed.

(* but the previous `frames` cannot, because the frame contains the
  state, which cannot be duplicated (this would violate the no-cloning
  theorem). *)
global lemma [P] _ (t, t' : _[adv]) :
  [t' < t] -> equiv(frame@t) -> equiv(frame@t').
Proof.
  intro A E.
  checkfail apply E exn ApplyMatchFailure.
Abort.
