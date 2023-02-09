include Basic.

(* Checking the treatment of bound variables in indirect cases for xor. *)

name n : index->message
name m : index->message

abstract ok : message
abstract ko : message

channel c

system !_i out(c,<n(i),seq(i:index => n(i))>).


axiom len_ok (i:index): len(ok) = len(n(i))
axiom len_ko (i:index): len(ko XOR m(i)) = len(n(i))
axiom len_ko_ok (i:index): len(ko XOR ok) = len(n(i)).

(* The main test, with a non-empty list of bound variables. *)
global goal _ (tau:timestamp[const],i:index[const]) : 
  [(forall (i0,i1:index) A(i0)<=tau => i1 <> i) = true] ->
  equiv(output@tau) ->
  equiv(output@tau, n(i) XOR diff(ok,m(i))).
Proof.
  intro H E.
  xor 1.
  rewrite H.
  (* Check that the right formula has been produced using H. *)
  rewrite if_true in 1.

  by namelength n(i),m(i); use len_ok with i.
  fresh 1; 1:auto.
  assumption.
Qed.

(* The same test, but giving the fresh name as argument to the xor tactic. *)
global goal _ (tau:timestamp[const],i:index[const]) : 
  [(forall (i0,i1:index) A(i0)<=tau => i1 <> i) = true] ->
  equiv(output@tau) ->
  equiv(output@tau, n(i) XOR diff(ok,m(i))).
Proof.
  intro H E.
  xor 1, n(i).
  rewrite H.
  (* Check that the right formula has been produced using H. *)
  rewrite if_true in 1.

  by namelength n(i),m(i); use len_ok with i.
  fresh 1; 1:auto.
  assumption.
Qed.
