include Core.
include WeakSecrecy.

system P = null.


global lemma[set:P/left; equiv:none] _:
  $((empty, empty) |> (zero)).
Proof.
  deduce 0.
  deduce.
Qed.

global lemma[set:P/left; equiv:P/left,P/left] _:
  $((empty, empty) |> (zero)).
Proof.
  deduce 0.
  deduce. 
Qed.

global lemma[set:P/left; equiv:none] _ (tau : timestamp[const]):
  $((frame@tau, frame@tau) |> (exec@tau)).
Proof.
  deduce 0.
  deduce.
Qed.

global lemma[set:P/left; equiv:none] _ (tau : timestamp[const]):
  $((frame@tau) |> (frame@(pred tau))).
Proof.
  deduce.
Qed.

global lemma[set:P/left; equiv:none] _ (tau : timestamp[const]):
  [exec@tau] -> $((frame@tau) |> (output@tau)).
Proof.
  intro H.
  deduce.
Qed.

global lemma[set:P/left; equiv:none] _ (tau : timestamp[const]):
  $((frame@tau) |> (output@tau)).
Proof.
  checkfail deduce exn ApplyMatchFailure.
Abort.

global lemma [any] _ (tau : timestamp[const]):
  [happens tau] -> [exec@tau] ->
  $(zero |> zero).
Proof.
  intro Hap E.
  deduce.
Qed.
