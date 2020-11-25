(* Authentication of the Basic Hash protocol, multiple tags. *)
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
lemma drf_ll (i : int) : is_lossless (drf i) by smt (drf_lluni).
lemma drf_uni (i : int) : is_uniform (drf i) by smt (drf_lluni).

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

(* Without initialization, with logs to express the authentication property. *)
module BasicHash0 (H : PRFs_Oracles) = {
  var tag_outputs   : (int * ptxt * ptxt) list
  var reader_forged : (int * ptxt * ptxt) list

  proc tag (i : int) : ptxt * ptxt = {
    var n, h;
    i <- if (n_tag <= i) then 0 else i;
    n <$ dnonce;
    h <@ H.f(i,n);
    (* We log the output message *)
    tag_outputs <- (i,n,h) :: tag_outputs;
    return (n, h);
  }    
  
  proc reader_i (i : int, n h : ptxt) : bool = {    
    var b;
    b <- H.check(i, n, h);
    return b;
  } 

  proc reader (n h : ptxt) : bool = {    
    var r, b, i;
    b <- false;
    i <- 0;
    while (i < n_tag) {
      r <- H.check(i, n, h);
      (* If the message is accepted but was not sent by a honest tag, 
         we log it. *)
      if (r && ! (mem tag_outputs (i,n,h))){ 
        reader_forged <- (i,n,h) :: reader_forged;
      }

      b <- b || r;
      i <- i + 1;
    }
    return b;
  }
}.

(* With initialization *)
module BasicHash (H : PRFs) = {
  module BH0 = BasicHash0(H)
  include BH0

  proc init () : unit = { 
    H.init(n_tag); 
    BasicHash0.tag_outputs <- [];
    BasicHash0.reader_forged <- [];
  }
}.

(*-----------------------------------------------------------------------*)
module type BasicHashT = {
  proc init () : unit
  proc tag (_ : int) : ptxt * ptxt
  proc reader (_: ptxt * ptxt) : bool
}.

module type BasicHashT0 = {
  include BasicHashT[-init]
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
  module BH = BH(H)
  module Adv = Adv (BH)

  proc main () = {
    BH.init ();
    Adv.a();
    return (exists x, mem BasicHash0.reader_forged x );
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
module type BasicHashF0 (H : PRFs_Oracles) = {
  include BasicHashT0
}.

(* The PRF/RF distinguisher is almost identical to the authentication game,
   except that it does not initialize the PRF. *)
module D (A : Adv) (BH : BasicHashF0) (F : PRFs_Oracles) = {
  module BH = BH(F)
  module A = A (BH)
  
  proc distinguish () = {
    BasicHash0.tag_outputs <- [];
    BasicHash0.reader_forged <- [];
    A.a();
    return (exists x, mem BasicHash0.reader_forged x ); 
  } 
}.

(*-----------------------------------------------------------------------*)
(* Given an adversary A against the Authentication Game, we build an
   an adversary B against the unforgeable PRF H. *)

(* The probability of winning the indistinguishability game against
   the RF is identical to the authentication game using the RF. *)
lemma eq_RF &m (A <: Adv {BasicHash, EUF_RF}) : 
    Pr[AuthGame(A, BasicHash, EUF_RF).main() @ &m : res] =
    Pr[EUF_PRF_IND(EUF_RF, D(A, BasicHash0)).main() @ &m : res]
by byequiv; auto; proc; inline *; wp; sim; auto. 

(* Idem with PRF *)
lemma eq_PRF &m (A <: Adv {BasicHash, PRFs}) : 
    Pr[AuthGame(A, BasicHash, PRFs).main() @ &m : res] =
    Pr[EUF_PRF_IND(PRFs, D(A, BasicHash0)).main() @ &m : res]
by byequiv; auto; proc; inline *; wp; sim; auto. 

(* The adversary cannot win the authentication game instantiated
    with the ideal unforgeable hash function. *)
lemma res_0 &m (A <: Adv {BasicHash, PRFs, EUF_RF}) : 
    Pr[AuthGame(A, BasicHash, EUF_RF).main() @ &m : res] = 0%r.
proof.
  byphoare; auto. 
  hoare; proc*; inline *; wp; sp. 
  call (_: BasicHash0.reader_forged = [] /\ EUF_RF.n = n_tag /\
           forall j x y, (EUF_RF.m.[(j,x)] <> None && oget EUF_RF.m.[(j,x)] = y)
                          => (j, x, y) \in BasicHash0.tag_outputs{hr}); auto.

  (* tag *)
  + proc; inline *; auto; sp.
    seq 1: (#pre); 1  : by conseq />; auto; smt().
    sp; if; 2: by conseq/>;auto;smt().
    by auto; smt(get_setE).

  (* reader *)
  + proc; inline *; conseq />.
    while (0 <= i <= n_tag /\ #pre) => //; 2 : by conseq />; auto; smt(n_tag_p).
    conseq />; auto => /> *; smt(get_setE).

  + by move => *; smt.
qed.

(* We conclude. *)
lemma auth0 &m (A <: Adv {BasicHash, PRFs, EUF_RF}) : 
    Pr[AuthGame(A, BasicHash, PRFs).main() @ &m : res] = 
      (   Pr[EUF_PRF_IND(PRFs,   D(A, BasicHash0)).main() @ &m : res] 
        - Pr[EUF_PRF_IND(EUF_RF, D(A, BasicHash0)).main() @ &m : res] ).
proof.
  rewrite (eq_PRF &m A) -(eq_RF &m A) (res_0 &m A); by smt ().
qed.
