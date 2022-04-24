set autoIntro=false.
(* set debugConstr=true. *)

aenc enc,dec,pk
hash h
name kenc:message
name khash:message
channel c
channel c2
name n:message
name r:message
name fr:message
name ideal:message
system null.

abstract ok : message.

system [test]
   (A:
    out(c, <enc(n,r,pk(kenc)) , h(enc(n,r,pk(kenc)),khash)>)
    |
    B:
    in(c,x);
    if h(fst(x), khash) = snd(x) then
      out(c,
        diff(h(ok,dec( fst(x),kenc)),ideal))).


(* we start with a first transitivity, from test/left to testCCA*)
system testCCA = [test/left] with gcca, enc(n,r,pk(kenc)).

(* we start with a second transitivity, from test/right to testCCAR*)
system testCCAR = [test/right] with gcca, enc(n,r,pk(kenc)).

(* we map the fresh value of testCCAr to the one of testCCA *)
system testCCAf = [testCCAR] with rename equiv(diff(n_CCA1,n_CCA)).

axiom [any] fst_pair: forall (x,y:message), fst(<x,y>)=x.
axiom [any] snd_pair: forall (x,y:message), snd(<x,y>)=y.

equiv [testCCA,testCCAf] tests.
Proof.
print.
enrich pk(kenc), n_CCA, r, h(enc(n_CCA,r,pk(kenc)),khash).

induction t.
prf 0.
yesif 0 => //.

expandall.
equivalent  try find  such that n = n
          in enc(n_CCA,r,pk(kenc)) else enc(n,r,pk(kenc)),
  enc(n_CCA,r,pk(kenc)) .
case (try find  such that n = n in enc(n_CCA,r,pk(kenc)) else enc(n,r,pk(kenc))) => //.
fa 4.
auto.

expand frame.
fa 4.
fa 5.
equivalent  exec@B, exec@pred(B) && (A<B && fst(input@B) = fst(output@A)  && snd(input@B) = snd(output@A)).
split.
expand exec,cond.
intro [ex Ha].
euf Ha.

intro Neq.
expand output.
rewrite fst_pair.
intro [Meq].
rewrite Meq => //.

intro [ex [Eq Eq2 Ord]].
expand exec,cond.
split => //.


fadup 5.
expand output.

ifeq 5,fst(input@B), fst(output@A).
intro _ => //.
help.
ifcond 5, exec@pred(B) && A<B => //.



equivalent        if exec@pred(B) && A < B then
         h(ok,
         try find  such that fst(output@A) = enc(n_CCA,r,pk(kenc))
         in n else dec(fst(output@A),kenc)),
       if exec@pred(B) && A < B then
         h(ok,n).
fa => //.
intro Ord.

expand output.
rewrite fst_pair.
case try find such that _ in n else _.
intro [_ Meq].
auto.
intro [Neg _] => //.

fa 5. fadup 5.
fa 5. fadup 5.
(* prf 5 *)

admit.

admit.
Qed.
