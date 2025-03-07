include Core.

op i0 : index.

op m (i : index) : message.

op format ['a 'b] : 'a -> 'b.
op read   ['a 'b] : 'b -> 'a.

game G = {
  var s = empty_set;

  oracle o (i : index) = {
    s := add (m i) s;
    return diff(i, i0);
  }

  oracle a = { 
    return 
      if subseteq s (singleton (read 42)) then diff(read 0, read 1)
  }    

  oracle b = { 
    return 
      if subseteq s (union (singleton (read 42)) (singleton (read 24))) then 
        diff(read "foo", read "bar")
  }    
}.

channel c.

(*-----------------------------------------------------------------*)
system P = null.
system Q = !_n out(c, format diff(n, i0)).

(* set verboseCrypto=true. *)

(*-----------------------------------------------------------------*)
global lemma [P] _ : 
  equiv(
   fun i => diff(i,i0), 
   diff(read[message,_] 0, read 1) (* need oracle `a` *)
  ).
Proof.
  crypto G.
  have A : forall (i:index), m i = read 42 by admit.
  assumption A.
Qed.

(*-----------------------------------------------------------------*)
(* same using `P` instead of a `fun` to require many calls to `o` *)
global lemma [Q] _ (t :_[adv]): 
  equiv(
   frame@t,
   diff(read[message,_] 0, read 1)
  ).
Proof.
  crypto G.
  have A : forall (n:index), A(n) <= t => m n = read 42 by admit.
  assumption A.
Qed.

(*-----------------------------------------------------------------*)
global lemma [P] _ : 
  equiv(
   fun i => diff(i,i0), 
   diff(read[message,_] "foo", read "bar") (* need oracle `b` *)
  ).
Proof.
  crypto G.
  have A : forall (i:index), m i = read 42 || m i = read 24 by admit.
  assumption A.
Qed.

(*-----------------------------------------------------------------*)
(* same using `P` instead of a `fun` to require many calls to `o` *)
global lemma [Q] _ (t :_[adv]): 
  equiv(
   frame@t,
   diff(read[message,_] "foo", read "bar") (* need oracle `b` *)
  ).
Proof.
  crypto G.
  have A : forall (n:index), A(n) <= t => m n = read 42 || m n = read 24 by admit.
  assumption A.
Qed.
