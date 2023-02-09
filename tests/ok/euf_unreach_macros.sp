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
goal _ (t : timestamp[param]) :
 happens(t) => output@t = h(n,k) => false.
Proof.
 intro Hap H.
 by euf H.
Qed.

(* starting from [s], there are collision *)
goal _ (t : timestamp[param]) :
 happens(t) => s@t = h(n,k) => false.
Proof.
 intro Hap H. 
 checkfail by euf H exn GoalNotClosed.
Abort.

(* same goal, but testing more precisely the condition generated *)
goal _ (t : timestamp[param]) :
 happens(t) => s@t = h(n,k) => exists(i:index), P(i) <= t && s@pred(P(i)) = n.
Proof.
 intro Hap H. 
 euf H => [i H1].
 by exists i.
Qed.

(*------------------------------------------------------------------*)
name nonce : index -> message.
mutable s1(i : index) : message = h(nonce(i),k).
mutable s2(i : index) : message = s1(i).

process Q(i:index) =
  out(c, s2(i)).

system [second] (!_i Q(i)).

goal [second] _ (t : timestamp[param]) (j : index[param]):
 happens(t) => output@t = h(nonce(j),k) => false.
Proof.
 intro Hap H. 
 checkfail by euf H exn GoalNotClosed. 
Abort.

(*------------------------------------------------------------------*)

mutable s3(i : index) : message = h(nonce(i),k).
mutable s4(i : index) : message = s3(i).

process R(i:index) =
  let x = s4(i) in
  out(c, x).

system [third] (!_i R(i)).

goal [third] _ (t : timestamp[param]) (j : index[param]):
 happens(t) => output@t = h(nonce(j),k) => false.
Proof.
 intro Hap H. 
 checkfail by euf H exn GoalNotClosed. 
Abort.
