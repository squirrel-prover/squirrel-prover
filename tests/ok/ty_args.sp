op foo ['a] : 'a.

axiom [any] _ : foo[message] = empty.

(* ---------------------------------------------------------------- *)
op bar ['a 'b] : ('a * 'b).

axiom [any] _ : bar[message, bool] = (empty, true).
