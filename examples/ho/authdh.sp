(* signed dh key exchange *)
channel c.

abstract ok : message

(*------------------------------------------------------------------*)
(* gdh group *)
type G
type E [large]

gdh gen, (^), ( ** ) where group:G exponents:E.

(*------------------------------------------------------------------*)
(* This assumes INT-CTXT + IND-CPA, and adds the rewrite rule:
   dec(enc(x,r,k),k) = x *)
senc enc, dec.

(*------------------------------------------------------------------*)
abstract E_e : E.
abstract inv_E : E -> E
abstract dlog : G -> E
abstract ofG : G -> message.
abstract toG : message -> G.

(* conversion of agent names into messages *)
abstract agent : index -> message.

axiom [any] agent_inj (A, B:index) :
  (agent(A) = agent(B)) = (A = B).
hint rewrite agent_inj.

abstract tag1:message.
abstract tag2:message.
axiom [any] tag_neq: (tag1 = tag2) = false.

(* signature *)
signature sign,checksign,pk.

axiom [any] sign_ax (x,y,k : message) : x = y => checksign(x, sign(y,k), pk(k)).

abstract error : G.

(* kdf *)
hash KDF.

name kKDF : message.

(* long term signing keys *)
name k : index -> message.

(* ephemerals for Alice  *)
name x : index * index * index -> E.

(* ephemerals for Bob  *)
name y : index * index * index -> E.

(* key derived by Alice(A, B, i) and Bob(A,B,j) *)
name dk : index * index * index * index -> message.

(* Alice(A,B): A sends g^x to B, receives g^y + signature, sends signature *)
process Alice (A:index, B:index, i:index) =
  let xA = x(A,B,i) in
  A1:out(c, ofG(gen^xA));
  in(c, mA);
  let gy = fst(mA) in
  let sA = snd(mA) in
  if checksign(<tag1,<agent(A),<gy, ofG(gen^xA)>>>, sA, pk(k(B))) then
    let gkA = toG(gy)^xA in
    let kA = KDF(ofG(gkA), kKDF) in
    A2:out(c, sign(<tag2,<agent(B), <ofG(gen^xA), gy>>>, k(A))).

(* Bob(A,B): B receives g^x from A, sends g^y + signature, receives signature *)
process Bob (A:index, B:index, j:index) =
  in(c, gx);
  let yB = y(A,B,j) in
  B1:out(c, <ofG(gen^yB), sign(<tag1,<agent(A), <ofG(gen^yB), gx>>>, k(B))>);
  in(c, sB);
  if checksign(<tag2,<agent(B), <gx, ofG(gen^yB)>>>, sB, pk(k(A))) then
    let gkB = toG(gx)^yB in
    let kB = KDF(ofG(gkB), kKDF) in
    B2:out(c, ok). 

process kdforacle (i:index) =
   in(c,x); O : 
   out(c, KDF(x,kKDF)).

process corrupt (A:index) =
  out(c, k(A)).

process protocol = (
  (!_A (!_B (!_i (Alice(A,B,i) | Bob(A,B,i))))) | 
  (!_A corrupt(A)) | 
  (!_O kdforacle(O))
).

system [default] protocol.

(*------------------------------------------------------------------*)
include Basic.

abstract Some : message -> message.
abstract None : message.
abstract oget : message -> message.
include Lib.

(*------------------------------------------------------------------*)
(* We prove the secrecy of the key derived by A. *)
goal [default] kA_secret (A,B,i:index, t:timestamp):
  happens(t) =>
  not (happens(corrupt(B))) =>
  happens(A2(A,B,i)) =>
  cond@A2(A,B,i) =>
  input@t = ofG(gkA(A,B,i)@A2(A,B,i)) =>
  false.
Proof.
  intro Hhap HB Hhap2 Hs He.
  euf Hs.
  (* case 1: B is corrupted *)
  + auto.
  (* case 2: the signature came from Alice(B,A,j): impossible thanks to the tags *)
   + by intro [_ _ [_ [U _]]]; rewrite tag_neq in U.
  (* case 3: the signature came from Bob *)
   + intro [_ j [_ [_ [_ [Hy _]]]]] /=; clear Hs.
     rewrite /gy in Hy.
     rewrite /gkA Hy /= in He.
     apply f_apply toG in He; simpl.

     by gdh He, gen.
Qed.

(*------------------------------------------------------------------*)
(* We prove the weak forward secrecy of the key derived by A. *)
goal [default] kA_weak_forward_secret (A,B,i:index, t:timestamp):
  happens(t) =>
  not (corrupt(B) < A2(A,B,i)) =>
  happens(A2(A,B,i)) =>
  cond@A2(A,B,i) =>
  input@t = ofG(gkA(A,B,i)@A2(A,B,i)) =>
  false.
Proof.
  intro Hhap HB Hhap2 Hs He.
  euf Hs.
  (* case 1: B is corrupted *)
  + auto.
  (* case 2: the signature came from Alice(B,A,j): impossible thanks to the tags *)
  + by intro [_ _ [_ [U _]]]; rewrite tag_neq in U.
  (* case 3: the signature came from Bob *)
  + intro [_ j [_ [_ [_ [Hy _]]]]] /=; clear Hs.
    rewrite /gy in Hy.
    rewrite /gkA Hy /= in He.
    apply f_apply toG in He; simpl.
    (* we use the GDH hypothesis *)
    by gdh He, gen.
Qed.

(*------------------------------------------------------------------*)
(* Agreement of A holds whenever B has not been corrupted before A's execution *)
goal [default] A_agreement (A,B,i:index):
   happens(A2(A,B,i)) =>
   not (corrupt(B) < A2(A,B,i)) =>
   (cond@A2(A,B,i) <=>
    exists (j:index),
      B1(A,B,j) < A2(A,B,i) && 
      gkA(A,B,i)@A2(A,B,i) = gen^(x(A,B,i) ** y (A,B,j)) &&
      fst (input@A2(A,B,i)) = fst (output@B1(A,B,j)) &&
      input@B1(A, B, j) = ofG (gen ^ xA(A, B, i)@A2(A, B, i)) &&
      checksign(<tag1,<agent A,<ofG (gen ^ y(A, B, j)),ofG (gen ^ x(A, B, i))>>>, 
                snd (input@A2(A,B,i)), 
                pk(k(B)))).
Proof.
  intro Hhap HB.
  split. 
  - intro Hc.
    rewrite /cond in Hc. 
    euf Hc.
    + (* case 1: B corrupted *)
      auto.

    + (* case 2: signature is from Alice(B,A,j) *)
      by intro [_ _ [_ [U _]]]; rewrite tag_neq in U.

    + (* case 3: signature is from Bob(A,B,j) *)
      intro [_ j [Ht [_ [_ [H1 H2]]]]].
      exists j; simpl.
      by rewrite /gkA H1 /xA /yB E_com. 

  - intro [j [H1 [H2 H3 H4 H5]]]. 
    rewrite /cond /sA. 
    have ->: gy(A, B, i)@A2(A, B, i) = ofG (gen ^ y(A, B, j)) by auto.
    have ->: ofG (gen ^ xA(A, B, i)@A2(A, B, i)) = ofG (gen ^ x(A, B, i)) by auto. 
    auto. 
Qed.

(*------------------------------------------------------------------*)
(* Agreement of B holds whenever A has not been corrupted before B's execution *)
goal [default] B_agreement (A,B,i:index):
   happens(B2(A,B,i)) =>
   not (corrupt(A) < B2(A,B,i)) =>
   cond@B2(A,B,i) =>
   exists (j:index),
     A2(A,B,j) < B2(A,B,i) && gkB(A,B,i)@B2(A,B,i) = gen^(x(A,B,j) ** y (A,B,i)).
Proof.
  intro Hhap HB Hc.
  rewrite /cond in Hc.
  have C := depends_default_B1_B2 _ A B i _ Hhap => //. 
  euf Hc.
    + (* case 1: B corrupted *)
      by intro []. 
    + (* case 2: signature is from Alice(B,A,j) *)
      intro [_ j [C0 [_ [_ [H _]]]]] //=; clear Hc.
      exists j => /=.
      have ?: happens(A2(A,B,j)) by case C0. 
      by rewrite /gkB H. 
    + (* case 3: signature is from Bob(A,B,j) *)
      intro [_ _ [_ [U _]]]. 
      by rewrite eq_sym tag_neq in U. 
Qed.

goal [any] aux (t, t' : timestamp) : (t <= pred t' && t <= t') <=> t <= pred t'.
Proof. auto. Qed.

(*------------------------------------------------------------------*)
(* Assumptions *)

(* Strong assumption, which could be weakened to a more realistic one 
   by adding a condition "only when checkG(x)" *)
axiom [any] ofG_toG (x:message) : ofG(toG(x)) = x.

(* => is from toG_ofG, <= from ofG_toG *)
goal [any] ofG_swap (x:message, y:G) : (x = ofG(y)) = (toG(x) = y).
Proof.
 rewrite eq_iff; split.
 by rewrite (f_apply toG x (ofG(y))). 
 by rewrite -(ofG_toG x).
Qed.

(*------------------------------------------------------------------*)
name nfresh : message.

(* Strong forward secrecy of A's key as long. *)
global goal [set:default/left; equiv:default/left, default/left]
  kA_strong_forward_secrecy (t, t0 : timestamp[const], A,B,i:index[const]) :
  [t = A2(A,B,i)] ->
  [t <= t0] ->
  [not (corrupt B < t)] ->
  equiv(
    frame@t0, 
    if cond@t then diff(kA(A,B,i)@t, nfresh)).
Proof.
  intro Heq Hhap Hcorrupt. 
  rewrite /kA. 
  prf 1 => /=. 
  rewrite (if_true _ n_PRF). {
    intro Cond.
    rewrite Heq in *.
    intro j H1 H2.
    have ? : O(j) <= t0 by case H1. 
    clear H1.
    rewrite eq_sym in H2. 
    by apply kA_weak_forward_secret in H2.
  }.
  fa 1.
  by fresh 2.
Qed.
