hash h
abstract m : message
name k : message
channel c
system
  A: in(c,x);
     if x=h(m,k) then
     out(c,x);
  B: out(c,h(m,k)).

(* TODO this should also work without out(c,x)
 *   i.e. with out(h(m,k)) in action A itself
 *   but euf is too imprecise and gives a goal
 *   with A<=A *)

goal happens(A) => False.
Proof.
  euf 0.
  (* B <= A is not possible, but cannot prove it yet *)
