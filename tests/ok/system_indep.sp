(*------------------------------------------------------------------*)
mutable tt : timestamp = init.

system [A] null.
system [B] null.

(*------------------------------------------------------------------*)
(* the system-independence check goes through if all systems are 
   the same single system. *)
global axiom [set:B/left; equiv:B/left, B/left] gfooB (t:timestamp): equiv(frame@t).
global goal  [set:B/left; equiv:B/left, B/left] _ : equiv(frame@(tt@init)).
Proof. have ? := gfooB (tt@init). Abort.

(*------------------------------------------------------------------*)
(* the system-independence check fails if there is more than one single system. *)
global axiom [set:B/left; equiv:B/left, B/right] gfooB' (t:timestamp): equiv(frame@t).
global goal  [set:B/left; equiv:B/left, B/right] _ : equiv(frame@(tt@init)).
Proof. checkfail have ? := gfooB' (tt@init) exn Failure. Abort.

(*------------------------------------------------------------------*)
(* the system-independence check fails if there is more than one single system. *)
global axiom [set:B/right; equiv:B/left, B/left] gfooB'' (t:timestamp): equiv(frame@t).
global goal  [set:B/right; equiv:B/left, B/left] _ : equiv(frame@(tt@init)).
Proof. checkfail have ? := gfooB'' (tt@init) exn Failure. Abort.

(*==================================================================*)
axiom [A] baba (x : timestamp[glob], y : timestamp) : x = y.

goal [A] _ (u : timestamp): false.
Proof.
  (* we can instantiate `baba` on SI terms *)
  have ? := baba init init.     

  (* we can instantiate `baba` second argument on a non-SI term *)
  have ? := baba init (diff(init,u)).

  (* we CANNOT instantiate `baba` first argument on a non-SI term *)
  checkfail (have ? := baba (diff(init,u)) init) exn Failure.
Abort.
