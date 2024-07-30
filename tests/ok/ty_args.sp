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

(* ---------------------------------------------------------------- *)
predicate Bar ['a] {} = [witness['a] = witness['a]].
predicate ( *=  ) ['a   ] {} (x,y : 'a) = [x = y].
predicate ( **= ) ['a 'b] {} (x,y : 'a) = [x = y].

system P = null.

type T.

global axiom [P] _ ['b] : 
  Bar['b] /\ Bar[bool] /\ 

  $(empty         *=    empty) /\ 
  $(empty         *=[_] empty) /\ 
  $(empty         *=[message] empty) /\
  $(witness['b]   *=['b] witness) /\ 
  $(witness[bool] *=[_] witness) /\

  $(empty         **=[_,T] empty) /\ 
  $(empty         **=[message, bool] empty) /\
  $(witness['b]   **=['b, bool] witness) /\ 
  $(witness[bool] **=[_, 'b] witness)
.
