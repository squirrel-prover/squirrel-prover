include Core. 
include Int. 
open Int.

op toI['a] : 'a -> index.
name n : index -> message.

system P = null.

let rec f  @system:P (x : int) with
| _ when x <= 0 -> empty
| _ when x > 0 -> <diff(n (toI x), empty), f (x - 1)>.
Proof. smt. Qed.
Proof. smt. Qed.

game G = {
  oracle o = { rnd n : message; return diff(n,empty); }
}.

global lemma _ @system:P (i:_[adv]) : equiv(f i).
Proof. 
  checkfail crypto G exn Failure.  
  (* Should fail as `i` is not const, and the type is not fixed+finite  *)
Abort.

(* global lemma _ @system:P (i:_[const]) : equiv(f i). *)
(* Proof.  *)
(*   crypto G.                     (* FEAT: could be ok, as `i` is `const` *) *)
(* Abort. *)
