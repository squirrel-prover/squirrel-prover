

hash h
name k : message
name n : message
name m : message
channel c

system let s = h(n,k) in out(c,s).

(* Testing that macros induced by a let definition
 * have the right number of parameters even in case of
 * a dummy input in the action. *)

goal _ (tau:timestamp[param]):
  happens(tau) => output@tau <> h(m,k).

Proof.
  intro Hap Heq.
  euf Heq. 
  auto.
Qed.

(* Testing that macro support computation does not ignore let bindings *)
goal _ (tau:timestamp[param]):
  happens(tau) => s@tau <> h(n,k).

Proof.
  intro Hap Heq. 
  checkfail by euf Heq exn GoalNotClosed.
Abort.
