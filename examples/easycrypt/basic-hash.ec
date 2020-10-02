(* Simple modeling of the Basic Hash protocol. *)
require import AllCore List FSet SmtMap.
require import Distr DBool.
require PRF.
require FelTactic.

(* Key space *)
type key.

(* Full, lossless and uniform distribution over keys. *)
op dkey: { key distr |     is_lossless dkey
                        /\ is_full dkey
                        /\ is_uniform dkey } as dkey_llfuuni.

(* Ptxt space *)
type ptxt.

(* Lossless and uniform distribution over ptxts (not full). *)
op dnonce: { ptxt distr |    is_lossless dnonce
                          /\ is_uniform dnonce } as dnonce_lluni.

(* Pair, first and second projections *)
op pair : ptxt -> ptxt -> ptxt.
op fst  : ptxt -> ptxt.
op snd  : ptxt -> ptxt.

axiom func_fst x y : fst (pair x y) = x.
axiom func_snd x y : snd (pair x y) = y.

(*-----------------------------------------------------------------------*)
(* PRF *)
op F : key -> ptxt -> ptxt.

clone import PRF as PRFt with
  type D <- ptxt,
  type R <- ptxt.

clone import PseudoRF as PRFi with
  type K <- key,
  op dK <- dkey,
  op F <- F
  proof * by smt(dkey_llfuuni).


(* RF *)
(* We assume the F is indistinguishable from a lossless and uniform distribution
    over ptxts (not full). *)
op drf: { ptxt distr |    is_lossless drf
                       /\ is_uniform drf } as drf_lluni.

op drfn (x : ptxt) = drf.

clone import RF as RFi with
  op dR <- drfn
  proof dR_ll.
realize dR_ll.
    move => *.
    have H : ((drfn x) = drf); 1: by auto.
    rewrite H.
    have := drf_lluni; auto.
qed.

(*-----------------------------------------------------------------------*)
(* Basic Hash protocol, with only one tag and one reader. *)
module BasicHash (H : PRF) = {

  proc init () : unit = { 
    H.init(); 
  }

  proc tag () : ptxt = {
    var n, x, h;
    n <$ dnonce;
    h <@ H.f(n);
    x <- pair n h;
    return x;
  }    
  
  proc reader (m : ptxt) : bool = {    
    var h, b;
    h <@ H.f(fst m);
    b <- snd m = h;
    return b;
  } 
}.

(* (* Basic Hash protocol, with n+1 tags and one reader. *) *)
(* module BasicHashN = { *)
(*   var ks : key list *)

(*   (* We always have at least one key. *) *)
(*   proc init (n : int) : unit = { *)
(*     var i, x; *)
(*     i <- 0; *)
(*     while (i <= n){ *)
(*       x <$ dkey; *)
(*       ks <- x :: ks; *)
(*     } *)
(*   } *)

(*   proc tag (i : int) : ptxt = { *)
(*     var k, n, x; *)
(*     n <$ dnonce; *)
(*     i <- if (size ks <= i) then 0 else i; *)
(*     k <- nth witness ks i; *)
(*     x <- pair n (H k n); *)
(*     return x; *)
(*   } *)

(*   proc reader (m : ptxt) : bool = { *)
(*     var i, b, k; *)
(*     i <- 0; *)
(*     b <- false; *)
(*     while (i < size ks){       *)
(*       k <- nth witness ks i; *)
(*       b <- b || snd m = H k (fst m); *)
(*     } *)
(*     return b; *)
(*   } *)
(* }. *)


(*-----------------------------------------------------------------------*)
module type BasicHashT = {
  proc init () : unit
  proc tag () : ptxt
  proc reader (_ : ptxt) : bool
}.

module type BasicHashT0 = {
  include BasicHashT[-init]
}.

(* Basic Hash, 1 tag, with logs. *)
module Log (BH : BasicHashT) = {
  var tag_outputs   : ptxt list
  var reader_forged : ptxt list

  proc init () : unit = { 
    BH.init ();
    tag_outputs <- [];
    reader_forged <- [];
  }

  proc tag () : ptxt = {
    var x;
    x <@ BH.tag ();
    tag_outputs <- x :: tag_outputs;
    return x;
  }    

  proc reader (m : ptxt) : bool = {    
    var b;
    b <- BH.reader(m);
    (* We log messages accepted by the reader that the tag never send. *)
    if (b && ! (mem tag_outputs m)){ 
      reader_forged <- m :: reader_forged;
    }
    return b;
  }    
}.

(* (* Log + init procedure *) *)
(* module LogF (BH : BasicHashT) = { *)
(*   proc init () : unit = {  *)
(*     BH.init (); *)
(*     Log.tag_outputs <- []; *)
(*     Log.reader_accepted <- []; *)
(*   } *)

(*   module Log = Log (BH) *)
(*   include Log *)
(* }. *)

(* Adversary against the Basic Hash protocol authentication *)
module type Adv (BH : BasicHashT0) = {
  proc a () : unit
}.

module type BasicHashF (H : PRF) = {
  include BasicHashT
}.

(* Basic Hash protocol authentication game *)
module AuthGame (Adv : Adv) (BH : BasicHashF) (H : PRF) = {
  module BH = Log(BH(H))
  module Adv = Adv (BH)

  proc main () = {
    BH.init ();
    Adv.a();
    return (exists (x : ptxt), mem Log.reader_forged x );
  }
}.

(*-----------------------------------------------------------------------*)
(* In our PRF/RF distinguisher, we must use a slightly different log,
   which is identical except that it does not initialize the BasicHash
   protocol. *)
module LogB (BH : BasicHashT0) = {
  proc init () : unit = { 
    Log.tag_outputs <- [];
    Log.reader_forged <- [];
  }

  proc tag () : ptxt = {
    var x;
    x <@ BH.tag ();
    Log.tag_outputs <- x :: Log.tag_outputs;
    return x;
  }    

  proc reader (m : ptxt) : bool = {    
    var b;
    b <- BH.reader(m);
    if (b && ! (mem Log.tag_outputs m)){ 
      Log.reader_forged <- m :: Log.reader_forged;
    }
    return b;
  }    
}.

module type BasicHashF0 (H : PRF_Oracles) = {
  include BasicHashT0
}.

(* The PRF/RF distinguisher is almost identical to the authentication game,
   except that it does not initialize the PRF. *)
module D (A : Adv) (BH : BasicHashF0) (F : PRF_Oracles) = {
  module BH = LogB(BH(F))
  module A = A (BH)
  
  proc distinguish () = {
    BH.init();
    A.a();
    return (exists (x : ptxt), mem Log.reader_forged x ); 
  } 
}.

(* Basic hash, without initialization *)
module BasicHash0 (H : PRF_Oracles) = {
  proc tag () : ptxt = {
    var n, x, h;
    n <$ dnonce;
    h <@ H.f(n);
    x <- pair n h;
    return x;
  }    

  proc reader (m : ptxt) : bool = {    
    var h, b;
    h <@ H.f(fst m);
    b <- snd m = h;
    return b;
  }    
}.

(*-----------------------------------------------------------------------*)
(* Given an adversary A against the Authentication Game, we want to
   build an adversary B against the PRF H, such that, roughly:
   Adv_Auth(A) ≤ Adv_PRF(B) + 1/card(nonce) 
   where card(nonce) is the cardinal of the support of the nonce 
   space. *)

(* The probability of winning the indistinguishability game against
   the RF is identical to the authentication game using the RF. *)
lemma eq_RF &m (A <: Adv {Log, BasicHash, RF}) : 
    Pr[AuthGame(A, BasicHash, RF).main() @ &m : res] =
    Pr[IND(RF, D(A, BasicHash0)).main() @ &m : res].
proof.
  byequiv; auto; proc; inline *; wp; sim; auto. 
qed.

(* Idem with PRF *)
lemma eq_PRF &m (A <: Adv {Log, BasicHash, PRF}) : 
    Pr[AuthGame(A, BasicHash, PRF).main() @ &m : res] =
    Pr[IND(PRF, D(A, BasicHash0)).main() @ &m : res].
proof.
  byequiv; auto; proc; inline *; wp; sim; auto. 
qed.

(* First game hope: we replace the PRF by a random function. *)
lemma auth0 &m (A <: Adv {Log, BasicHash, PRF, RF}) : 
    Pr[AuthGame(A, BasicHash, PRF).main() @ &m : res] = 
      (   Pr[IND(PRF, D(A, BasicHash0)).main() @ &m : res] 
        - Pr[IND(RF, D(A, BasicHash0)).main() @ &m : res] )
      + Pr[AuthGame(A, BasicHash, RF).main() @ &m : res].
proof.
  rewrite (eq_RF &m A) (eq_PRF &m A); by smt ().
qed.

(*-----------------------------------------------------------------------*)
(* Finally, we need to bound the probability for the adversary to win
   the authentication game by the collision probability w.r.t. TODO *)

(* Bound on the number of calls to the reader by the adversary. *)
op qreader : int.

(* This changes a Basic Hash implementations by bounding the number of
   queries forwarded to reader by qreader. *)
module BHBounder (BH : BasicHashT0) = { 
  var q0 : int

  proc tag = BH.tag

  proc reader (m : ptxt) = {
    var x;
    
    if (q0 < qreader) {
      x <@ BH.reader(m);
      q0 <- q0 + 1;
    }
    return x;
  }
}.

(* This allows an adversary to call reader at most q times. *)
module ABounder (A : Adv) (BH : BasicHashT0) = {
  module BH = BHBounder(BH)
  module A = A(BH)

  proc a () = {
    BHBounder.q0 <- 0;
    A.a();
  }
}.

(* TBD *)
op bnd : real.
op stepbnd (x : int) : real.

lemma coll (A <: Adv {Log, BasicHash, RF}) : 
    phoare[AuthGame(ABounder(A), BasicHash, RF).main : true ==> res] <= bnd. 
proof.
 proc.
 fel 0
   BHBounder.q0 (* counter *)
   stepbnd (* probability of setting bad when the counter increases. *)
   qreader (* maximal value of the counter *)
   (exists (x : ptxt), mem Log.reader_forged x) (* bad event *)
   [] true (* inv  *).
 (* the sum of stepbnd, for i in [0; qreader[, is upper-bounded by bnd *)
 admit.  

 (* If the adversary wins, then bad is true, and the counter is at
    most qreader. *)
 simplify; move => &m0 H; split. 
   + admit.
   + proc.
