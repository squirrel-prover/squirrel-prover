(* Authentication of a simplified Basic Hash protocol, with only one tag. *)
require import AllCore List FSet SmtMap.
require import Distr DBool.
require FelTactic.

(*-----------------------------------------------------------------------*)
(* Key space *)
type key.

(* Full, lossless and uniform distribution over keys. *)
op dkey: { key distr |     is_lossless dkey
                        /\ is_full dkey
                        /\ is_uniform dkey } as dkey_llfuuni.

(*-----------------------------------------------------------------------*)
(* Ptxt space *)
type ptxt.

(* Lossless and uniform distribution over ptxts (not full). *)
op dnonce: { ptxt distr |    is_lossless dnonce
                          /\ is_uniform dnonce } as dnonce_lluni.
lemma dnonce_ll (i : int) : is_lossless dnonce by smt (dnonce_lluni).
lemma dnonce_uni (i : int) : is_uniform dnonce by smt (dnonce_lluni).

hint exact random : dnonce_ll.

(*-----------------------------------------------------------------------*)
(* PRF *)
op F : key -> ptxt -> ptxt.

module type PRF = {
  proc init () : unit
  proc f(x : ptxt) : ptxt
  proc check(x : ptxt, s : ptxt) : bool
}.

module type PRF_Oracles = {
  include PRF[-init]
}.

module PRF = {
  var k : key
  
  proc init() : unit = {
    PRF.k <$ dkey;
  }
  
  proc f(x : ptxt) : ptxt = {
    return F k x;
  }

  proc check(x : ptxt, s : ptxt) = {
    return (F k x = s);
  }
}.

(* Unforgeable RF *)
(* We assume that: 
   i) the hash function is indistinguishable from a lossless and uniform
   distribution over ptxts (not full).
   ii) the hash function is unforgeable.
   
   ii) is a consequence of i) whenever the hash function image set is large. *)
op drf: { ptxt distr |    is_lossless drf
                       /\ is_uniform drf } as drf_lluni.

module EUF_RF = {
  var m : (ptxt, ptxt) fmap
  
  proc init() : unit = {
    m <- empty;
  }
  
  proc f(x : ptxt) : ptxt = {
    var r : ptxt;
    
    if (x \notin m) {
      r <$ drf;
      m.[x] <- r;
    }
    
    return oget m.[x];
  }

  proc check(x : ptxt, s : ptxt) = {
    return (x \in m && oget m.[x] = s);
  }
}.

(*-----------------------------------------------------------------------*)
(* Basic Hash protocol, with only one tag and one reader. *)

(* Without initialization *)
module BasicHash0 (H : PRF_Oracles) = {
  proc tag () : ptxt * ptxt = {
    var n, h;
    n <$ dnonce;
    h <@ H.f(n);
    return (n, h);
  }    
  
  proc reader (n h : ptxt) : bool = {    
    var b;
    b <- H.check(n, h);
    return b;
  } 
}.

(* With initialization *)
module BasicHash (H : PRF) = {
  module BH0 = BasicHash0(H)
  include BH0

  proc init () : unit = { 
    H.init(); 
  }
}.

(*-----------------------------------------------------------------------*)
module type BasicHashT = {
  proc init () : unit
  proc tag () : ptxt * ptxt
  proc reader (_: ptxt * ptxt) : bool
}.

module type BasicHashT0 = {
  include BasicHashT[-init]
}.

(* Basic Hash, 1 tag, with logs. *)
module Log (BH : BasicHashT) = {
  var tag_outputs   : (ptxt * ptxt) list
  var reader_forged : (ptxt * ptxt) list

  proc init () : unit = { 
    BH.init ();
    tag_outputs <- [];
    reader_forged <- [];
  }

  proc tag () : ptxt * ptxt = {
    var x;
    x <@ BH.tag ();
    tag_outputs <- x :: tag_outputs;
    return x;
  }    

  proc reader (m : ptxt * ptxt) : bool = {    
    var b;
    b <- BH.reader(m);
    (* We log messages accepted by the reader that the tag never send. *)
    if (b && ! (mem tag_outputs m)){ 
      reader_forged <- m :: reader_forged;
    }
    return b;
  }    
}.

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
    return (exists x, mem Log.reader_forged x );
  }
}.


(*-----------------------------------------------------------------------*)
(* Indistinguishability game for an unforgeable PRF. *)
module type Distinguisher (F : PRF_Oracles) = {
  proc distinguish(): bool
}.

module EUF_PRF_IND (F : PRF) (D : Distinguisher) = {
  proc main(): bool = {
    var b;

    F.init();
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

  proc tag () : ptxt * ptxt = {
    var x;
    x <@ BH.tag ();
    Log.tag_outputs <- x :: Log.tag_outputs;
    return x;
  }    

  proc reader (m : ptxt * ptxt) : bool = {    
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
    Pr[EUF_PRF_IND(EUF_RF, D(A, BasicHash0)).main() @ &m : res]
by byequiv; auto; proc; inline *; wp; sim; auto. 

(* Idem with PRF *)
lemma eq_PRF &m (A <: Adv {Log, BasicHash, PRF}) : 
    Pr[AuthGame(A, BasicHash, PRF).main() @ &m : res] =
    Pr[EUF_PRF_IND(PRF, D(A, BasicHash0)).main() @ &m : res]
by byequiv; auto; proc; inline *; wp; sim; auto. 

(* The adversary cannot win the authentication game instantiated
    with the ideal unforgeable hash function. *)
lemma res_0 &m (A <: Adv {Log, BasicHash, PRF, EUF_RF}) : 
    Pr[AuthGame(A, BasicHash, EUF_RF).main() @ &m : res] = 0%r.
proof.
  byphoare; auto. 
  hoare; proc*; inline *; wp; sp. 
  call (_: Log.reader_forged = [] /\ 
           forall x y, (EUF_RF.m.[x] <> None && oget EUF_RF.m.[x] = y)
                        => (x, y) \in Log.tag_outputs{hr}); auto.
  (* tag *)
  + proc; inline *; auto.
    seq 2: (#pre /\ x0 = n); wp; 1 : by rnd => *; auto.
    if; 2 : by auto; smt().
    by wp; rnd; auto; smt(get_setE).

  (* reader *)
  + by proc; inline *; auto => /#.

  + by move => *; smt. 
qed.

(* We conclude. *)
lemma auth0 &m (A <: Adv {Log, BasicHash, PRF, EUF_RF}) : 
    Pr[AuthGame(A, BasicHash, PRF).main() @ &m : res] = 
      (   Pr[EUF_PRF_IND(PRF,    D(A, BasicHash0)).main() @ &m : res] 
        - Pr[EUF_PRF_IND(EUF_RF, D(A, BasicHash0)).main() @ &m : res] ).
proof.
  by rewrite (eq_PRF &m A) -(eq_RF &m A) (res_0 &m A); smt ().
qed.
