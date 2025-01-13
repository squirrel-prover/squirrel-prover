include Core.

(*------------------------------------------------------------------*)
game G0 = {
  let v : int = #init;
  let u = (v,42);
  let w = #init;
 
  oracle o = { return diff (u,w); }
}.

system null.

global lemma _ : equiv(diff( (24,42), (0,1) )).
Proof.
  checkfail crypto G0 (v : 24) (w : (0,2)) exn Failure.
  checkfail crypto G0 (v : 24) (w : (1,1)) exn Failure.
  checkfail crypto G0 (v : 10) (w : (0,1)) exn Failure.
  crypto G0 (v : 24) (w : (0,1)). 
Qed.

(*------------------------------------------------------------------*)
(* we check that variables are initialized with values that the
   adversary can compute (`a` is purposedly ignored in the 
   output). *)
game G1 = {
  let a : string = #init;
 
  oracle o = { return diff (0,1); }
}.

global lemma _ : equiv(diff(0,1)).
Proof.
 (* the diff-term `diff("a", "b")` is not bi-deducible *)
  checkfail crypto G1 (a : diff("a", "b")) exn Failure.
  crypto G1 (a : "foo").
Qed.

(*------------------------------------------------------------------*)
op enc : int -> message -> string -> message.

game G = {
  let pk = #init;

  oracle enc m0 m1 = {
    rnd r : message;
    return diff(enc m0 r pk, enc m1 r pk);
    }
}.

name r : message.

global lemma _ : equiv(diff(enc 0 r "bar", enc 1 r "bar")).
Proof.
  checkfail crypto G (pk : "foo") exn Failure.
  crypto G (pk : "bar").
Qed.
