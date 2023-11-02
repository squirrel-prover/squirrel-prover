include Basic.

(* Keyed hash function with an incorrect PRF game.
   The game is broken: the hash oracle can be called after the
   challenge oracle, on the same query. *)
abstract h : message*message -> message.

game PRF = {
  rnd key : message;
  var l = empty_set;

  oracle ohash x = {
    l := add x l;
    return h(x,key) 
  }

  oracle challenge x = {
    rnd r : message;
    var old_l = l;
    l := add x l;
    return if mem x old_l then h(x,key) else diff(r, h(x,key))
  }
}.

(* ---------------------------------------------------------------------- *)

system null.

name k : message.
name nfresh : message.
name n : index -> message.

(* Basic test. *)
global lemma _ : equiv(diff(nfresh,h(zero,k))).
Proof.
  crypto PRF.
Qed.

(* Test: precise handling of conditional. *)
global lemma _ (i,j:index[const]) :
  equiv(h(n i,k),
        if i <> j then diff(nfresh, h(n j,k)) else h(n j, k)).
Proof.
  crypto PRF => //.
Qed.

(* Prove that crypto assumption is absurd. *)

global lemma [default/left,default/left] Oops : equiv(diff(nfresh,h(zero,k)),h(zero,k)).
Proof.
  crypto PRF.
Qed.

lemma [default/left] _ : false.
Proof.
  assert nfresh = h(zero,k).
  by rewrite equiv Oops.
  by fresh Meq.
Qed.
