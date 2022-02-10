set autoIntro=false.

hash h (1)
name k : message

abstract a : message
abstract b : message
abstract f : message->message

system null.

goal _ (i,j:index) : f(h(i,a,k)) = h(j,b,k) => a = b.
Proof.
  nosimpl(intro Heq).
  nosimpl(euf Heq; intro Eqab). 
  (* Since i=j is possible, EUF should not dismiss the hash of a. *)
  nosimpl(assumption).
Qed.
