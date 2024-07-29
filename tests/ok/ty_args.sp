op foo ['a] : 'a.

axiom [any] _           : foo[message] = empty.
axiom [any] foo_ax ['a] : foo['a] = witness.

(* ---------------------------------------------------------------- *)
op bar ['a 'b] : ('a * 'b).

axiom [any] _              : bar[message, bool] = (empty, true).
axiom [any] bar_ax ['a 'b] : bar['a, 'b] = witness.

(* ---------------------------------------------------------------- *)
axiom [any] witness_empty_message : witness[message] = empty.
axiom [any] witness_empty_bool    : witness[bool]    = true.

(* ---------------------------------------------------------------- *)
lemma [any] _ : foo[message] = empty && foo[bool] = true.
Proof.
  have Hm := foo_ax[message].
  have Hb := foo_ax[bool].
  split.
  + checkfail rewrite Hb exn NothingToRewrite.
    rewrite Hm.
    apply witness_empty_message.
  + checkfail rewrite Hm exn NothingToRewrite.
    rewrite Hb.
    apply witness_empty_bool.
Qed.
