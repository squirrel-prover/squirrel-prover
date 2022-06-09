

channel c.

abstract a : message.
abstract b : message.

op f : message = a.

system [A] !_i O: (in(c,x); out(c, <x,f>)).
system [B] !_i O: (in(c,x); out(c, a)).

goal [A] _ : a = b => f = b.
Proof. by intro ->. Qed.

(* FIXME: should work, see FIXME in `expand_head_once` in `Match.ml` *)
(* goal [any] _ : a = b => f = b. *)
(* Proof. by intro ->. Qed. *)

goal [B] _ (t : timestamp, i : index) : 
  happens(t) => t = O(i) => a = b => output@t = b.
Proof. 
  by intro Hap H ->.
Qed.

(* check that rewriting does not unfold too much: if after 
   unfolding we can not match at head position, we fail *)
goal [A] _ (t : timestamp, i : index) : 
  happens(t) => t = O(i) => a = b => output@t = b.
Proof. 
  checkfail intro Hap H -> exn NothingToRewrite.
Abort.
