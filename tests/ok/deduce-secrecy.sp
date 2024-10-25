include WeakSecrecy.

system P = null.


global lemma[set:P/left; equiv:none] toto1:
  $((empty, empty) |> (zero)).
Proof.
  deduce 0.
  deduce.
Qed.

global lemma[set:P/left; equiv:P/left,P/left] toto2:
  $((empty, empty) |> (zero)).
Proof.
  deduce 0.
  deduce. 
Qed.

global lemma[set:P/left; equiv:none] toto3 (tau : timestamp[const]):
  $((frame@tau, frame@tau) |> (exec@tau)).
Proof.
  deduce 0.
  deduce.
Qed.

global lemma[set:P/left; equiv:none] toto4 (tau : timestamp[const]):
  $((frame@tau) |> (frame@(pred tau))).
Proof.
  deduce.
Qed.

global lemma[set:P/left; equiv:none] toto5 (tau : timestamp[const]):
  [exec@tau] -> $((frame@tau) |> (output@tau)).
Proof.
  intro H.
  deduce.
Qed.

global lemma[set:P/left; equiv:none] toto6 (tau : timestamp[const]):
  $((frame@tau) |> (output@tau)).
Proof.
  checkfail deduce exn ApplyMatchFailure.
Abort.

global lemma [any] toto7 (tau : timestamp[const]):
  [happens tau] -> [exec@tau] ->
  $(zero |> zero).
Proof.
  intro Hap E.
  checkfail deduce exn Failure.
Abort.
