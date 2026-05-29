include Core.
include Set.

(* ----------------------------------------------------------------- *)
system P = null.

(* ----------------------------------------------------------------- *)
namespace T.
  type t[enum,finite].

  op z : t. 
  op pred : t -> t.

  axiom pred_ax @system:any x : x <> z => pred x < x.
end T.
open T.

let rec f ~opaque (x : t) : message = if x = z then empty else f (pred x).
Proof. intro *. by apply pred_ax. Qed.

(* ----------------------------------------------------------------- *)
game Empty = { }.

global lemma _ @system:P (t : t[adv]) : equiv(f t).
Proof. 
  checkfail crypto Empty exn Failure.
  (* this should fail because `t` of a type `enum`
     and `crypto` can only do recursion over a type which is
     `finite+fixed`. *)
Abort.
