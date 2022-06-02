

channel c.

abstract a : message.
abstract b : message.

op f : message = a.

system [A] !_i O: (in(c,x); out(c, <x,f>)).
system [B] !_i O: (in(c,x); out(c, a)).

axiom [any] fst_pair (x, y: message) : fst (<x, y>) = x.
hint rewrite fst_pair.

goal [A] _ (t : timestamp, i : index) : 
  happens(t) => t = O(i) => input@t = b => fst(output@t) = b.
Proof. 
  intro Hap H U /=.
  clear H Hap U.
  (* clear to check `/=` indeed simplified `fst(output@t)` into `input@t`,
     which is in turn simplified into `true` by `U` *)
  assumption.
Qed.

goal [B] _ (t : timestamp, i : index) : 
  happens(t) => t = O(i) => input@t = b => fst(output@t) = b.
Proof. 
  intro Hap H U /=.
  clear H Hap U.
  checkfail assumption exn NotHypothesis.
Abort.
