

(* Checking the treatment of bound variables in indirect cases for fresh. *)

name n : index * index -> message

abstract mtest : index -> boolean

channel c

system !_k A: out(c,try find k such that mtest(k) in n(k, k)).

(* The main test, with a non-empty list of bound variables. *)
goal _ (tau:timestamp) (i,j:index) :
  happens(tau) => output@tau = n(i, j) => i = j.
Proof.
  intro H H1.
  by fresh H1 => [_ _]. 
Qed.
