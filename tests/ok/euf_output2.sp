

hash h
name k:message
channel c

name n : message
name m : message

(* TODO having a new n under the ! should be equivalent;
        it does not seem to be the case at the moment *)

system !_a out(c,h(n,k)).

goal unforgeable (tau:timestamp[param]):
  happens(tau) => output@tau <> h(m,k).

Proof.
  by intro Hap Heq; euf Heq.
Qed.
