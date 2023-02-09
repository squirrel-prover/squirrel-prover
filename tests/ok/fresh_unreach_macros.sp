set newInduction=true.

channel c

name n : message
name m : message

abstract f : message -> message

mutable s : message = n.

process P (i : index) =
  in(c,x);
  s := f(s);
  out(c, x).

system !_i P (i).

(* starting from [frame], [n] is fresh *)
global goal _ (t : timestamp[const]) :
 [happens(t)] -> equiv(frame@t) -> equiv(frame@t, diff(n,m)).
Proof.
 intro Hap H.

 by fresh 1.
Qed.

(* starting from [s], [n] is *not* fresh *)
global goal _ (t : timestamp[const]) :
 [happens(t)] -> equiv(s@t) -> equiv(s@t, diff(n,m)).
Proof.
 intro Hap H. 

 checkfail by fresh 1 exn GoalNotClosed.
Abort.


(* same as the first goal, but without any premise by induction *)
global goal _ (t : timestamp[const]) :
 [happens(t)] -> equiv(frame@t, diff(n,m)).
Proof.
 induction t.
 intro t Ind Hap.

 case t => A.
 
 by fresh 1.

 fresh 1; 1:auto.
 destruct A as [_ _].
 expandall; fa 0.
 by apply Ind.
Qed.

(*------------------------------------------------------------------*)
(* test reachability fresh *)

(* starting from [frame], [n] is fresh *)
goal _ (t : timestamp[const]) :
 happens(t) => frame@t <> n.
Proof.
 intro Hap M.

 by fresh M.
Qed.

(* starting from [s], [n] is *not* fresh *)
goal _ (t : timestamp[const]) :
 happens(t) => s@t <> n.
Proof.
 intro Hap M. 

 checkfail by fresh M exn GoalNotClosed.
Abort.


(*------------------------------------------------------------------*)
(* more complex system  *)

mutable s1 : message = empty.
mutable s2 : message = empty.
mutable s3 : message = empty.

process Q (i : index) = 
  in(c,x);
  s1 := s;
  out(c, x).

process R (i : index) = 
  in(c,x);
  s2 := s1;
  out(c, x).

system [second] (!_i Q: Q (i) | !_i R: R (i)).

(* starting from [frame, s3], [n] is fresh *)
global goal [second] _ (t : timestamp[const]) :
 [happens(t)] -> equiv(frame@t, s3@t) -> equiv(frame@t, s3@t, diff(n,m)).
Proof.
 intro Hap H.

 by fresh 2.
Qed.

(* starting from [s2], [n] is *not* fresh because it can be reached through:
  s2 -> s1 -> s -> n *)
global goal [second] _ (t : timestamp[const]) :
 [happens(t)] -> equiv(s2@t) -> equiv(s2@t, diff(n,m)).
Proof.
 intro Hap H. 

 checkfail by fresh 1 exn GoalNotClosed.
Abort.

(*------------------------------------------------------------------*)
(* test reachability fresh *)

(* starting from [frame], [n] is fresh *)
goal [second] _ (t : timestamp[const]) :
 happens(t) => frame@t <> n.
Proof.
 intro Hap M.

 by fresh M.
Qed.

(* starting from [s2], [n] is *not* fresh *)
goal [second] _ (t : timestamp[const]) :
 happens(t) => s2@t <> n.
Proof.
 intro Hap M. 

 checkfail by fresh M exn GoalNotClosed.
Abort.
