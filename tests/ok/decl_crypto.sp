

channel c.

type T
type C
type L  [large]
type R  [large]
type LP [large]

abstract f : index -> message.

abstract to_T : message -> T.
abstract from_T : T -> message.

(*------------------------------------------------------------------*)
(* Hash function *)

hash myhash where m:T h:T k:L.

process Hash =
 in(c,m);
 let mT = to_T (m) in
 new k : L;
 let a = myhash(mT,k) in
 out (c, from_T(a)).


(*------------------------------------------------------------------*)
(* Asymmetric encryption *)

aenc enc, dec, pkgen where ptxt:T ctxt:C rnd:R pk:LP sk:L.

process Aenc =
 in(c,m);
 let mT = to_T (m) in
 new sk : L;
 let pk : LP = pkgen(sk) in
 new r : R;
 let c : C = enc(mT,r,pk) in
 let d : T = dec(c,sk) in
 out (c, empty).

(*------------------------------------------------------------------*)
(* Symmetric encryption *)

senc sencr, sdecr where ptxt:T ctxt:C rnd:R k:L.

process Senc =
 in(c,m);
 let mT = to_T (m) in
 new k : L;
 new r : R;
 let c : C = sencr(mT,r,k) in
 let d : T = sdecr(c,k) in
 out (c, empty).

(*------------------------------------------------------------------*)
(* Signatures encryption *)

signature sign, checksign, spk where m:T sig:C sk:L pk:LP.

process Signature =
 in(c,m);
 let mT = to_T (m) in
 new sk : L;
 let mypk : LP = spk(sk) in
 let s : C = sign(mT,sk) in
 let ch : boolean = checksign(mT, s, mypk) in
 out (c, empty).

