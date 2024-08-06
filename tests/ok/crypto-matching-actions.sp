include Core.

set verboseCrypto = true.

abstract encr : message -> message -> message -> message.
abstract baccepte : message -> message -> bool.

(* CCA2 *)
game FOO = {
  rnd key : message;
  oracle foo (m0,m1 : message) = {
    rnd seed: message;
    return encr diff(m0,m1) key seed
  }
}.

channel c.
name seedA_enc1:message.
name sk_mix: message.

process Voter  (v : message) = 
  let cm = v in
  in(c,sb);
  let acc = baccepte cm sb in
  $vote : out (c,  
   (encr diff( if acc then cm, zero) sk_mix seedA_enc1)).


process Alice (v:message) = Voter(v)


action Avote : 0.

mutable box ( i:index) :  message = zero.

process mixer_vote_collect
(cmA : message)  
= 
!_i ( 
    let acc = baccepte cmA (input@Avote) in
    in(c,m);
    box(i):= 
      if m = encr diff(if acc then cmA,zero) (sk_mix) seedA_enc1 
      then (  cmA)
      else zero
  ).


abstract shuffle : (index -> message) -> message.
process mixer_vote_publish =
  let Box = fun i => box i in 
  let commits = shuffle Box in
  out(c,  commits).



system Foo = 
   in(c,v0) ; 
   V_1 : out(c,zero);
   let cmA = v0 in
   Start  : out(c,empty);
   ((MVC : mixer_vote_collect (cmA))
   | (MVP : mixer_vote_publish                      )
   | (A : Alice(v0) )
 ).



global lemma [Foo] _ (t:_[const]) : [happens(t)] -> equiv(frame@t). 
Proof. 
intro *.
crypto FOO (key:sk_mix).
+ auto.
+ intro i. intro H0. rewrite not_exists_1 in H0. 
destruct H0.
destruct H1.
destruct H1.
have H2:= H0 i.
simpl.
assert Avote < MVC(i) || MVC(i) < Avote as Hl.
auto.
case Hl.
auto.
auto.
+ intro i i0.
  intro *.
  destruct H0.
  destruct H1.
  destruct H1.
  rewrite not_or in H0.
  rewrite not_or in H1.
  destruct H0.
  destruct H1.
  assert MVC(i) < MVC(i0) || MVC(i0) < MVC(i) as Hl by auto.
  rewrite not_exists_1 in H2, H3.
  have H4:= H2 i0.
  have H5:= H3 i.
  case Hl.
  auto.
  auto.
Qed.  
