(* Simple modeling of the Basic Hash protocol, multiple tags. *)
require import AllCore List FSet SmtMap.
require import Distr DBool.
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

(*-----------------------------------------------------------------------*)
(* multiple PRF *)
op F : key -> ptxt -> ptxt.

module type PRFs = {
  proc init (n : int) : unit
  proc f(i : int, x : ptxt) : ptxt
  proc check(i : int, x : ptxt, s : ptxt) : bool
}.

module type PRFs_Oracles = {
  include PRFs[-init]
}.

module PRFs = {
  var ks : key list
  
  proc init(n : int) : unit = {
    var i, k;
    i <- 0;
    while (i < n){
     k <$ dkey;
     ks <- k :: ks;
    } 
  }
  
  proc f(i : int, x : ptxt) : ptxt = {
    var k;
    i <- if (size ks <= i) then 0 else i;
    k <- nth witness ks i;
    return F k x;
  }

  proc check(i : int, x : ptxt, s : ptxt) = {
    var k;
    i <- if (size ks <= i) then 0 else i;
    k <- nth witness ks i;
    return (F k x = s);
  }
}.

(* Unforgeable multiple RF *)
(* We assume that: 
   i) the hash functions are indistinguishable from a lossless and uniform
   distributions over ptxts (not full).
   ii) the hash functions are unforgeable.
   
   ii) is a consequence of i) whenever the hash function image set is large. *)
op drf (i : int) : ptxt distr.
axiom drf_lluni (i : int) : is_lossless (drf i) /\ is_uniform (drf i).

module EUF_RF = {
  var n : int
  var m : (int * ptxt, ptxt) fmap
  
  proc init(i : int) : unit = {
    n <- i;
    m <- empty;
  }
  
  proc f(i : int, x : ptxt) : ptxt = {
    var r : ptxt;
    i <- if (n <= i) then 0 else i;

    if ((i,x) \notin m) {
      r <$ drf i;
      m.[(i,x)] <- r;
    }
    
    return oget m.[(i,x)];
  }

  proc check(i : int, x : ptxt, s : ptxt) = {
    i <- if (n <= i) then 0 else i;
    return ((i,x) \in m && oget m.[(i,x)] = s);
  }
}.

(*-----------------------------------------------------------------------*)
(* Basic Hash protocol, multiple tags and one reader. *)

op n_tag : int.
axiom n_tag_p : 0 < n_tag.  (* We have at least one tag. *)

(* Without initialization *)
module BasicHash0 (H : PRFs_Oracles) = {
  proc tag (i : int) : ptxt * ptxt = {
    var n, h;
    i <- if (n_tag <= i) then 0 else i;
    n <$ dnonce;
    h <@ H.f(i,n);
    return (n, h);
  }    
  
  proc reader (i : int, n h : ptxt) : bool = {    
    var b;
    i <- if (n_tag <= i) then 0 else i;
    b <- H.check(i, n, h);
    return b;
  } 
}.

(* With initialization *)
module BasicHash (H : PRFs) = {
  module BH0 = BasicHash0(H)
  include BH0

  proc init () : unit = { 
    H.init(n_tag); 
  }
}.

(*-----------------------------------------------------------------------*)
module type BasicHashT = {
  proc init () : unit
  proc tag (_ : int) : ptxt * ptxt
  proc reader (_: int * ptxt * ptxt) : bool
}.

module type BasicHashT0 = {
  include BasicHashT[-init]
}.

(* Basic Hash, multiple tags, with logs. *)
module Log (BH : BasicHashT) = {
  var tag_outputs   : (int * ptxt * ptxt) list
  var reader_forged : (int * ptxt * ptxt) list

  proc init () : unit = { 
    BH.init ();
    tag_outputs <- [];
    reader_forged <- [];
  }

  proc tag (i : int) : ptxt * ptxt = {
    var x, y;
    (x,y) <@ BH.tag (i);
    i <- if (n_tag <= i) then 0 else i;
    tag_outputs <- (i,x,y) :: tag_outputs;
    return (x,y);
  }    

  proc reader (i : int, x y : ptxt) : bool = {    
    var b;
    b <- BH.reader(i,x,y);
    (* We log messages accepted by the reader that the tag never send. *)
    i <- if (n_tag <= i) then 0 else i;
    if (b && ! (mem tag_outputs (i,x,y))){ 
      reader_forged <- (i,x,y) :: reader_forged;
    }
    return b;
  }    
}.

(* Adversary against the Basic Hash protocol authentication *)
module type Adv (BH : BasicHashT0) = {
  proc a () : unit
}.

module type BasicHashF (H : PRFs) = {
  include BasicHashT
}.

(* Basic Hash protocol authentication game *)
module AuthGame (Adv : Adv) (BH : BasicHashF) (H : PRFs) = {
  module BH = Log(BH(H))
  module Adv = Adv (BH)

  proc main () = {
    BH.init ();
    Adv.a();
    return (exists x, mem Log.reader_forged x );
  }
}.


(*-----------------------------------------------------------------------*)
(* Distinguisher against n_tag PRFs. *)
module type Distinguisher (F : PRFs_Oracles) = {
  proc distinguish(): bool
}.

(* Indistinguishability game for unforgeable PRFs. *)
module EUF_PRF_IND (F : PRFs) (D : Distinguisher) = {
  proc main(): bool = {
    var b;

    F.init(n_tag);
    b <@ D(F).distinguish();
    return b;
  }
}.

(*-----------------------------------------------------------------------*)
(* In our PRF/RF distinguisher, we must use a slightly different log,
   which is identical except that it does not initialize the BasicHash
   protocol. *)
module AuxLog (BH : BasicHashT0) = {
  proc init () : unit = { 
    Log.tag_outputs <- [];
    Log.reader_forged <- [];
  }

  proc tag (i : int) : ptxt * ptxt = {
    var x, y;
    (x,y) <@ BH.tag (i);
    i <- if (n_tag <= i) then 0 else i;
    Log.tag_outputs <- (i,x,y) :: Log.tag_outputs;
    return (x,y);
  }    

  proc reader (i : int, x y : ptxt) : bool = {    
    var b;
    b <- BH.reader(i,x,y);
    (* We log messages accepted by the reader that the tag never send. *)
    i <- if (n_tag <= i) then 0 else i;
    if (b && ! (mem Log.tag_outputs (i,x,y))){ 
      Log.reader_forged <- (i,x,y) :: Log.reader_forged;
    }
    return b;
  }    
}.

module type BasicHashF0 (H : PRFs_Oracles) = {
  include BasicHashT0
}.

(* The PRF/RF distinguisher is almost identical to the authentication game,
   except that it does not initialize the PRF. *)
module D (A : Adv) (BH : BasicHashF0) (F : PRFs_Oracles) = {
  module BH = AuxLog(BH(F))
  module A = A (BH)
  
  proc distinguish () = {
    BH.init();
    A.a();
    return (exists x, mem Log.reader_forged x ); 
  } 
}.

(*-----------------------------------------------------------------------*)
(* Given an adversary A against the Authentication Game, we build an
   an adversary B against the unforgeable PRF H. *)

(* The probability of winning the indistinguishability game against
   the RF is identical to the authentication game using the RF. *)
lemma eq_RF &m (A <: Adv {Log, BasicHash, EUF_RF}) : 
    Pr[AuthGame(A, BasicHash, EUF_RF).main() @ &m : res] =
    Pr[EUF_PRF_IND(EUF_RF, D(A, BasicHash0)).main() @ &m : res].
proof.
  byequiv; auto; proc; inline *; wp; sim; auto. 
qed.

(* Idem with PRF *)
lemma eq_PRF &m (A <: Adv {Log, BasicHash, PRFs}) : 
    Pr[AuthGame(A, BasicHash, PRFs).main() @ &m : res] =
    Pr[EUF_PRF_IND(PRFs, D(A, BasicHash0)).main() @ &m : res].
proof.
  byequiv; auto; proc; inline *; wp; sim; auto. 
qed.

(* The adversary cannot win the authentication game instantiated
    with the ideal unforgeable hash function. *)
lemma res_0 &m (A <: Adv {Log, BasicHash, PRFs, EUF_RF}) : 
    Pr[AuthGame(A, BasicHash, EUF_RF).main() @ &m : res] = 0%r.
proof.
  byphoare; auto. 
  hoare; proc*; inline *; wp; sp. 
  call (_: Log.reader_forged = [] /\ EUF_RF.n = n_tag /\
           forall j x y, (EUF_RF.m.[(j,x)] <> None && oget EUF_RF.m.[(j,x)] = y)
                          => (j, x, y) \in Log.tag_outputs{hr}); auto.

  (* tag *)
  + proc; inline *; auto. 
  seq 6: (#pre /\ x0 = n /\ i1 = i0 /\ i0 = if n_tag <= i then 0 else i); wp.
   - by rnd; auto; smt (n_tag_p).
   - case ((i1, x0) \notin EUF_RF.m).
    * rcondt 1 => //; wp; rnd; auto.
     move => &hr [[[Hl Hind] [Heq1 [Heq2 Heq3]]] Hin] r H0; 
     do 2! (split; [ 1 : smt ()]);
     move => j x y H1.
     case (i1{hr} = j /\ x0{hr} = x) => Hx. case: Hx => Hj Hx.
     - left; split => //=. by rewrite -Hj Heq2 Heq3; auto. by smt ().
     - right. smt.
    * rcondf 1; auto; move => &hr [[[Hl [Ht Hind]] Heq] Hin].
      do 2! (split; [ 1 : smt ()]). 
      move => j x y H1; right; apply Hind; apply H1.

  (* reader *)
  + proc; inline *; auto => /=.
  move => &hr [hyp1 hyp2]; split => //. by smt.

  + move => &hr hyp; split => //; do 2! (split; [ 1 : smt ()]). 
    move => Ht x H; by smt.
qed.

(* We conclude. *)
lemma auth0 &m (A <: Adv {Log, BasicHash, PRFs, EUF_RF}) : 
    Pr[AuthGame(A, BasicHash, PRFs).main() @ &m : res] = 
      (   Pr[EUF_PRF_IND(PRFs,   D(A, BasicHash0)).main() @ &m : res] 
        - Pr[EUF_PRF_IND(EUF_RF, D(A, BasicHash0)).main() @ &m : res] ).
proof.
  rewrite (eq_PRF &m A) -(eq_RF &m A) (res_0 &m A); by smt ().
qed.
