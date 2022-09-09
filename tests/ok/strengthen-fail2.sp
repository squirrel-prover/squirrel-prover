

channel c.

name na : message

mutable S(i:index) : message = zero.

name n : index -> message.
name m : index -> message.

system (!_i S(i) := diff(n(i), m(i)); out(c, zero)).

global goal _ (t :timestamp) :
  [happens(t)] ->
  equiv(seq(i:index => S(i)@pred(t))) ->
  equiv(seq(i:index => S(i)@t)).
Proof.
  intro Hap H.
 
  checkfail (apply H) exn ApplyMatchFailure.
Abort.

