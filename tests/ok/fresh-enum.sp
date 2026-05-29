include Core.
include Set.

(* ----------------------------------------------------------------- *)
system P = null.

(* ----------------------------------------------------------------- *)
namespace T.
  type t[finite].          (* not fixed *)

  op z : t. 
  op pred : t -> t.

  axiom pred_ax @system:any x : x <> z => pred x < x.
end T.
open T.

name n : t -> message.

let rec f ~opaque (x : t) : message = 
  <n x, if x = z then empty else f (pred x)>.
Proof. intro *. by apply pred_ax. Qed.

(* ----------------------------------------------------------------- *)
game Empty = { }.

global lemma _ @system:P (t,t' : t[adv]) : equiv(f t, n t').
Proof. 
  fresh 1. (* fresh does not require `t` to be `fixed` *)
Abort.
