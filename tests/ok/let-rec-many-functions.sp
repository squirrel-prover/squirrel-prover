(* Test user-defined `let rec` on types other than timestamp.
   Check that independent recursive definition
   over the same well-founded type are not mixed-up by Squirrel. *)
channel c. 
system P = !_i A: out(c,empty).

name n : index -> message.

op p : index -> index.
op q : index -> index.

let rec f @system:P (t : timestamp) with
| init -> empty
| A i when happens t -> <n (p i), f (pred t)>
| _ when not(happens t) -> empty.
Proof. auto. Qed.

(* identically to `f` *)
let rec g @system:P (t : timestamp) with
| init -> empty
| A i when happens t -> <n (q i), g (pred t)>
| _ when not(happens t) -> empty.
Proof. auto. Qed.

lemma _ @system:P (att : _ -> message[adv]) (tf,tg:_[const]) (i:_[const]):
  att(f tf, g tg) = n i => false.
Proof.
  intro H. 
  checkfail fresh H exn Failure.
  (* We cannot operate over two distinct groups of recursive
     functions. We must define them simultaneously for that. *)
Abort.
