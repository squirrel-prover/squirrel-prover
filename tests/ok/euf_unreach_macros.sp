set autoIntro=false.
set newInduction=true.

channel c

name n : message
name m : message
name k : message

hash h

mutable s : message = n.


process P (i : index) =
  in(c,x);
  s := h(s,k);
  out(c, x).

system !_i P (i).

(* starting from [frame], euf find no collision *)
goal _ (t : timestamp) :
 happens(t) => output@t = h(n,k) => false.
Proof.
 intro Hap H.
 by euf H.
Qed.

(* starting from [s], there are collision *)
goal _ (t : timestamp) :
 happens(t) => s@t = h(n,k) => false.
Proof.
 intro Hap H. 
 checkfail by euf H exn GoalNotClosed.
Abort.

(* same goal, but testing more precisely the condition generated *)
goal _ (t : timestamp) :
 happens(t) => s@t = h(n,k) => exists(i:index), P(i) <= t && s@pred(P(i)) = n.
Proof.
 intro Hap H. 
 euf H => H1 H2.
 by exists i.
Qed.
