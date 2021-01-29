hash h
name k:message
channel c

name n : message
name m : message

(* TODO having a new n under the ! should be equivalent;
        it does not seem to be the case at the moment *)

system !_a out(c,h(n,k)).

goal unforgeable :
  forall (tau:timestamp),
  output@tau <> h(m,k).

Proof.
  by intro tau Heq; euf Heq; auto.
Qed.
