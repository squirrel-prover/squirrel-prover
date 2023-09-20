include Basic.

mutable pre  : message = empty
mutable s    : message = empty
mutable post : message = empty

abstract v : message

channel c

system
  !_i
  in(c,x);

  let pre_glob = s in
  pre := <s,x>;

  s := <s,x>;

  post := <s,x>;
  let post_glob = s in
  out(c,s).

(* --------------------------------------------------------- *)
lemma _ (a:index): 
  happens(A a) => 
  pre@A a = <s@pred(A a),input@A a>.
Proof.
 intro _.
 rewrite /pre.
 apply eq_refl. 
Qed.

lemma _ (a:index): 
  happens(A a) => 
  pre@A a = <s@A a,input@A a>.
Proof.
 intro _.
 rewrite /pre.
 checkfail apply eq_refl exn ApplyMatchFailure.
Abort.

(* --------------------------------------------------------- *)
lemma _ (a:index): 
  happens(A a) => 
  s@A a = <s@pred(A a),input@A a>.
Proof.
 intro _.
 rewrite /s.
 apply eq_refl. 
Qed.

lemma _ (a:index): 
  happens(A a) => 
  s@A a = <s@A a,input@A a>.
Proof.
 intro _.
 rewrite /s.
 checkfail apply eq_refl exn ApplyMatchFailure.
Abort.

(* --------------------------------------------------------- *)
lemma _ (a:index): 
  happens(A a) => 
  post@A a = <s@pred(A a),input@A a>.
Proof.
 intro _.
 rewrite /post.
 checkfail apply eq_refl exn ApplyMatchFailure.
Abort.

lemma _ (a:index): 
  happens(A a) => 
  post@A a = <s@A a,input@A a>.
Proof.
 intro _.
 rewrite /post.
 apply eq_refl. 
Qed.
