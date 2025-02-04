(*******************************************************************************
YUBIHSM

[1] R. Künnemann, "Foundations for analyzing security APIs in the symbolic and
computational model", 2014.

Y   -> S   : <pid,<nonce,otp>>
S   -> HSM : <<pid,kh>,<aead,otp>>
HSM -> S   : ctr
S   -> Y   : accept

with
- aead = enc(<k,pid,sid>,mkey)
- otp = enc(<sid,ctr>,npr,k)

PUBLIC DATA
- kh, pid
SECRET DATA KNOWN BY EACH PARTY
- YubiKey(pid): k(pid), sid(pid), ctr(pid)
- Server: { sid(pid), ctr(pid) | pid }
- HSM: mkey, { k(pid), sid(pid) | pid }

COMMENTS
- The last message "otp || nonce || hmac || status" is unclear and
  not modelled at all and replaced by "accept".
  It was also not modelled in [1].

- The otp is an encryption of a triple (sid, ctr, npr).
  It is modelled here as a randomized encryption of a pair (sid, ctr).

- enc is assumed to be AEAD (we do not use the associated data).

- In [1], they "over-approximate in the case that the Yubikey increases the
  session token by allowing the adversary to instantiate the rule for any
  counter value that is higher than the previous one".
  Here, we model the incrementation by 1 of the counter.

- As in [1], we model the two counters (session and token counters) as a single
  counter.

- In [1], the server keeps in memory the mapping between public and
  secret identities of the Yubikeys. As far as we understand, this
  does not reflect the YubiHSM specification: secret identities have  to
  be protected by the YubiHSM.  Instead, we choose to keep the
  necessary information to map public to private identities in the
  AEADs (we simply add the public identity to the AEADs plaintext).

- Diff terms are here to model a real system and an ideal system.
  The purpose of the ideal system is to replace the key inside the AEAD by a
  dummy one, in order to be able to use the intctxt tactic for the third
  security property (injective correspondence).

HELPING LEMMAS
- counter increase
- valid decode

SECURITY PROPERTIES
The 3 security properties as stated in [1].
- Property 1: no replay counter
- Property 2: injective correspondence
- Property 3: monotonicity

Properties 1 and 3 are established directly on the real system.
Property 2 is proved in 2 steps: first an equivalence is established
between the real system and the ideal one, and then the property
is proved on the ideal system. The reach equiv
tactic allows one to combine these two steps, and to conclude.
*******************************************************************************)
set timeout=10.

(* AEAD symmetric encryption scheme: IND-CCA + INT-CTXT *)
senc enc,dec

(*------------------------------------------------------------------*)
(* protocol constants *)
abstract endplug  : message
abstract accept   : message
abstract setup_ok : message

(*------------------------------------------------------------------*)
(* counters initial value *)
abstract cinit : message
(* counter successor *)
abstract mySucc : message -> message

(*------------------------------------------------------------------*)
(* Encoding of a public identity as a message.
   This encoding is injective (this is axiomatized later). *)
abstract mpid: index -> message

(* secret identity *)
name sid: index -> message

(*------------------------------------------------------------------*)
(* public key handle kh to reference the AES master key mkey *)
abstract kh: message
name mkey: message

(*------------------------------------------------------------------*)
(* working key k(pid) of yubikey `pid`, stored inside the AEAD *)
name k: index -> message
(* Dummy key used in AEAD idealized so that the key does not occur in
   plaintext anymore in the idealized system *)
name k_dummy: index -> message

(*------------------------------------------------------------------*)
(* counters *)
mutable YCtr(i:index) : message = cinit
mutable SCtr(i:index) : message = cinit

(*------------------------------------------------------------------*)
(* authentication server's database for each pid *)
mutable AEAD(pid:index) : message = zero.

(*------------------------------------------------------------------*)
channel cY
channel cS
channel cHSM

(* Order over counters. Assumed transitive and strict later through axioms. *)
abstract (~<): message -> message -> boolean.

(* When the key is plugged for yubikey `pid`, the counter is incremented. *)
process yubikeyplug (pid:index) =
  in(cY,x1);
  YCtr(pid) := mySucc(YCtr(pid));
  out(cY,endplug).

name nonce : index * index -> message
name npr : index * index -> message

(* When the key is pressed on the `j`-th session of yubikey `pid`:
   - an otp is sent with the current value of the counter,
   - the counter is incremented. *)
process yubikeypress (pid:index,j:index) =
  in(cY,x2);
  let ctr = YCtr(pid) in
  YCtr(pid) := mySucc(YCtr(pid));
  let menc = enc(<sid(pid),ctr>,npr(pid,j),k(pid)) in
  out(cY,<mpid(pid), <nonce(pid,j), menc>>).

(* When the server receives a message for pid:
   - it checks whether it corresponds to a pid in its database,
   - it retrieves the AEAD and kh associated to this pid and asks the HSM to
   decode the received otp,
   - it checks that the counter inside the otp (received from the HSM) is
   strictly greater than the counter associated to the token,
   - if so, this counter value is used to update the database.
   In our modelling, the server's request to the HSM (to retrieve k(pid)
   and sid(pid)) has been inlined.
 *)
process server (pid:index) =
  in(cS,x); (*x = <pid,<nonce, cipher>> with cipher = enc(<sid,cpt>,r, k)*)
  let cipher = snd(snd(x)) in
  let deccipher = dec(cipher,k(pid)) in
  let xcpt = snd(deccipher) in
  if fst(x) = mpid(pid) &&
     deccipher<>fail &&
     fst(deccipher) = sid(pid) &&
     SCtr(pid) ~< xcpt then
  SCtr(pid) := xcpt;
  out(cS,accept).

(*------------------------------------------------------------------*)
(* The attacker can read/write AEAD stored in the server's database. *)
process read_AEAD (pid:index) =
  out(cS,AEAD(pid)).

process write_AEAD (pid:index)=
  in(cS,x);
  AEAD(pid) := x.

(*------------------------------------------------------------------*)
(* model for the rule YSM_AEAD_YUBIKEY_OTP_DECODE of the HSM. *)
process YSM_AEAD_YUBIKEY_OTP_DECODE (pid:index) =
  in(cHSM,xdata);
  (* xdata = <<pid,kh>, <aead, otp>> with
       otp  = enc(<sid,cpt>,k)
       aead = enc(<k,<pid,sid>>,mkey)*)
   if fst(xdata) = <mpid(pid),kh> then
    let aead = fst(snd(xdata)) in
    let otp = snd(snd(xdata)) in

    let aead_dec = dec(aead,mkey) in

    let otp_dec = dec(otp,diff(fst(aead_dec), k(pid))) in

    if aead_dec <> fail &&
       otp_dec <> fail &&
       fst(otp_dec) = snd(snd(aead_dec)) &&
       mpid(pid) = fst(snd(aead_dec))
    then
      out(cHSM, snd(otp_dec)).

(*------------------------------------------------------------------*)
(* real system with ideal system *)
system !_pid
  new rinit;
  AEAD(pid) :=
    enc(<diff(k(pid),k_dummy(pid)), <mpid(pid), sid(pid)>>, rinit, mkey);
  Setup: out(cS, accept); (
  (!_j Plug   : yubikeyplug(pid)                 ) |
  (!_j Press  : yubikeypress(pid,j)              ) |
  (!_j Server : server(pid)                      ) |
  (!_j Read   : read_AEAD(pid)                   ) |
  (!_j Write  : write_AEAD(pid)                  ) |
  (!_j Decode : YSM_AEAD_YUBIKEY_OTP_DECODE(pid))).

(*------------------------------------------------------------------*)
(* AXIOMS *)

include Real.

axiom [any] orderTrans (n1,n2,n3:message): n1 ~< n2 => n2 ~< n3 => n1 ~< n3.

axiom [any] orderStrict(n1,n2:message): n1 = n2 => n1 ~< n2 => False.

axiom [any] mpid_inj (pid, pid':index): mpid(pid) = mpid(pid') => pid = pid'.

axiom [any] pair_ne_fail (x,y: message) : <x,y> <> fail.

hint smt orderTrans.
hint smt orderStrict.
hint smt mpid_inj.
hint smt pair_ne_fail.

abstract c_pair : message.
abstract (++) : message -> message -> message.
axiom [any] len_pair (x, y : message) : len(<x,y>) = (len(x) ++ len(y) ++ c_pair).

hint smt len_pair.

(* Utilities for simplifying some diff expressions. *)

lemma len_diff (x,y:message) : len(diff(x,y)) = diff(len(x),len(y)).
Proof.
  by project.
Qed.

(*------------------------------------------------------------------*)
(* LIBRAIRIES *)

lemma [any]  dec_enc (x,y,z:message) : dec(enc(x,z,y),y) = x.
Proof. auto. Qed.
hint rewrite dec_enc.

(* instances of f_apply *)
lemma [any] dec_apply (x,x',k : message): x = x' => dec(x,k) = dec(x',k).
Proof. auto. Qed.

(*------------------------------------------------------------------*)
(* HELPING LEMMAS - counter increase *)


lemma counterIncrease (t:timestamp, pid : index) :
  happens(t) =>
  t > init && exec@t =>
    SCtr(pid)@pred(t) ~< SCtr(pid)@t ||
    SCtr(pid)@t = SCtr(pid)@pred(t).
Proof.
 smt  ~steps:27385.
Qed.

(* The counter SCpt(ped) increases (not strictly) between t' and t
when t' < t. *)
lemma counterIncreaseBis:
  forall (t:timestamp), forall (t':timestamp), forall (pid:index),
    happens(t) =>
    exec@t && t' < t =>
    ( SCtr(pid)@t' ~< SCtr(pid)@t ||
      SCtr(pid)@t = SCtr(pid)@t').
Proof.
  induction.
  use counterIncrease; smt ~prover:CVC5_stringscounterexamples  ~steps:48576.
Qed.

(*------------------------------------------------------------------------------
SECURITY PROPERTIES 1 (no replay) AND 3 (monotonicity)
These two properties are proved directly on the real system, since they do not
rely on the intctxt tactic.
------------------------------------------------------------------------------*)

lemma noreplayInv (j, j', pid:index):
   happens(Server(pid,j),Server(pid,j')) =>
   exec@Server(pid,j') && Server(pid,j) < Server(pid,j') =>
   SCtr(pid)@Server(pid,j) ~< SCtr(pid)@Server(pid,j').
Proof.
  use counterIncreaseBis; smt ~provers:CVC5_stringscounterexamples ~steps:71121. 
Qed.

lemma noreplay (j, j', pid:index):
  happens(Server(pid,j')) =>
  exec@Server(pid,j') =>
  Server(pid,j) <= Server(pid,j') =>
  SCtr(pid)@Server(pid,j)= SCtr(pid)@Server(pid,j')=>
  j = j'.
Proof.
  use noreplayInv; smt  ~steps:25121. 
Qed.

(*------------------------------------------------------------------*)
lemma monotonicity (j, j', pid:index):
  happens(Server(pid,j'),Server(pid,j)) =>
  exec@Server(pid,j') && exec@Server(pid,j) &&
  SCtr(pid)@Server(pid,j) ~< SCtr(pid)@Server(pid,j') =>
  Server(pid,j) < Server(pid,j').
Proof.
 use noreplayInv; smt  ~steps:80710. 
Qed.


(*------------------------------------------------------------------------------
SECURITY PROPERTY 2 (injective correspondence)
The proof of this property is done in 2 steps.
- We first establish the equivalence between the real system and the ideal one
  (in which the key inside the AEAD are replaced by a dummy one).
  This corresponds to the lemma injective_correspondence_equiv.
- Then, we use the rule REACH-EQUIV (through the tactic rewrite equiv) in order
  to replace the real system by the ideal one, so that we only have to prove the
  security property on the ideal system.
  This corresponds to the lemma injective_correspondence.

Beforehand, we prove some helping lemmas:
- valid_decode, in order to characterize when the AEAD decoding process is valid;
- if_aux, a lemma used to rewrite a conditional;
- equiv_real_ideal_enrich_XXX, a serie of lemmas establishing the equivalence
between the real system and an ideal one, using sequences to enrich the frame.
------------------------------------------------------------------------------*)

(*------------------------------------------------------------------*)
(* First property of AEAD decoding. *)
lemma valid_decode (t : timestamp) (pid,j : index):
  (t = Decode(pid,j) || t = Decode1(pid,j)) =>
  happens(t) =>
  (aead_dec pid j@t <> fail) = 
  (exists(pid0 : index),
   Setup(pid0) < t &&
   AEAD(pid0)@Setup(pid0) = aead pid j@t).
Proof.
  intro Eq Hap.
  rewrite eq_iff; split.

  + (* Left => Right *)
    intro AEAD_dec.
    case Eq;
    expand aead_dec;
    intctxt AEAD_dec => // [pid0 AEAD_eq];
    by exists pid0.

  + (* Right => Left *)
    intro [pid0 [Clt H]].
    case Eq;
    expand aead_dec;
    rewrite -H /AEAD /=;
    apply pair_ne_fail.
Qed.

(* Using the `valid_decode` lemma, we can characterize when the full
   decoding check goes through. *)
lemma valid_decode_charac (t : timestamp) (pid,j : index):
  (t = Decode(pid,j) || t = Decode1(pid,j)) =>
  happens(t) =>
  ( aead_dec pid j@t <> fail &&
    otp_dec pid j@t <> fail &&
    fst(otp_dec pid j@t) = snd(snd(aead_dec pid j@t)) &&
    mpid(pid) = fst(snd(aead_dec pid j@t)) )
  =
  ( AEAD(pid)@Setup(pid) = aead pid j@t &&
    dec(otp pid j@t,k(pid)) <> fail &&
    fst(dec(otp pid j@t,k(pid))) = sid(pid) ).
Proof.
use valid_decode.
project; smt  ~steps:43921.
Qed.


(*------------------------------------------------------------------*)
(* Auxiliary simple lemma, used to rewrite one of the conditional
   equality in the then branch. *)
lemma if_aux (b,b0,b1 : boolean) (x,y,z,u,v:message):
   if b && (x = y && b0) && b1 then
     snd(dec(z,diff(fst(dec(y,u)),v))) =
   if b && (x = y && b0) && b1 then
    snd(dec(z,diff(fst(dec(x,u)),v))).
Proof. 
project; smt  ~steps:23373. 
Qed.

set showStrengthenedHyp=true.

name keyFresh : message.

(*------------------------------------------------------------------*)
global lemma equiv_real_ideal_enrich (t : timestamp[const]):
  [happens(t)] ->
  equiv(
    frame@t,
    seq(pid:index => AEAD(pid)@t),
    seq(pid:index => if Setup(pid) <= t then AEAD(pid)@Setup(pid)),
    seq(pid:index => sid(pid)),
    seq(pid,j:index => npr(pid,j)),
    seq(pid,j:index => nonce(pid,j)),
    seq(pid:index => k(pid)),
    seq(pid:index => k_dummy(pid))
  ).
Proof.
  dependent induction t => t Hind Hap.
  case t => Eq;
  (try (repeat destruct Eq as [_ Eq];
       rewrite /* in 0;
       rewrite /AEAD in 1;
       rewrite le_lt // -le_pred_lt in 2;
       by apply ~inductive Hind (pred(t)))).

  + (* init *)
    rewrite /*.
    by rewrite if_false in 1.

  + (* Setup(pid) *)
    repeat destruct Eq as [_ Eq].
    splitseq 2: (fun (pid0 : index) => pid = pid0).
    constseq 2:
      (fun (pid0 : index) => pid = pid0 && Setup(pid0) <= t) (AEAD(pid)@t)
      (fun (pid0 : index) => pid <> pid0 ||
                          (pid = pid0 && not (Setup(pid0) <= t))) zero.
      - simpl;smt  ~steps:22759.
      - simpl;smt  ~steps:24083.
      - rewrite if_then_then in 3.
        assert (forall(pid0 : index), (not (pid = pid0) && Setup(pid0) <= t) = (Setup(pid0) < t))
        as H. smt  ~steps:23987.
        rewrite /= H -le_pred_lt in 3.
        rewrite /AEAD in 1.
        fa 1.
        rewrite /AEAD in 4.
        rewrite /* in 0.
        cca1 2; [1:auto].
        rewrite !len_pair in 2.
        rewrite len_diff in 2.
        rewrite namelength_k namelength_k_dummy in 2. 
        simpl ~diffr. 
        remember
          zeroes (namelength_message ++ (len (mpid pid) ++ len (sid pid) ++ c_pair) ++ c_pair)
          as tlen => Eq_len.
        (* transitivity reasoning, to get rid of the key *)
        trans 2 : enc (tlen, rinit(pid), keyFresh).
        * have ->:
           diff(
             enc (tlen, rinit(pid), mkey),
             enc (tlen, rinit(pid), keyFresh))
           =
           enc (tlen, rinit(pid), diff(mkey,keyFresh))
          by project. 
          rewrite Eq_len.
            enckp 2, enc(_, rinit(pid), diff(mkey, keyFresh)), keyFresh;
            1: auto.

          fa 2; fa 2.
          fresh 4; 1:auto.
          fresh 3; 1:auto.
          rewrite /* in 0.
          by apply Hind (pred t).
        * have ->:
            diff(
              enc (tlen, rinit(pid), keyFresh),
              enc (tlen, rinit(pid), mkey))
            =
            enc (tlen, rinit(pid), diff(keyFresh, mkey)) by project.
          rewrite Eq_len; enckp 2; 1: auto.
          fa 2; fa 2.
          fresh 4; 1:auto.
          fresh 3; 1:auto.
          refl.

  + (* Decode(pid,j) *)
    repeat destruct Eq as [_ Eq].
    rewrite /AEAD in 1.
    rewrite le_lt // -le_pred_lt in 2. 
   depends Setup(pid), t by auto => H.
    rewrite /frame /exec /output /cond in 0.
    fa 0; fa 1; fa 1.

    rewrite valid_decode_charac //.
    (* rewrite the content of the then branch *)
    rewrite /otp_dec /aead_dec if_aux /= in 2.
    fa 2.
    rewrite /aead /otp in 1,2.
    fa !(_ && _). fa 1.
    simpl ~diffr.
    rewrite -(if_true (Setup(pid) <= pred t) _ zero) in 1 => //.
    rewrite !dec_enc !fst_pair.
    by apply Hind (pred(t)).

  + (* Decode1(pid,j) *)
    repeat destruct Eq as [_ Eq].
    rewrite /AEAD in 1.
    rewrite le_lt // -le_pred_lt in 2.
    depends Setup(pid), t by auto => H.
    rewrite /frame /exec /output /cond in 0.
    fa 0; fa 1; fa 1.
    rewrite valid_decode_charac //.
    rewrite /otp /aead.
    fa _ && _, not (_), !_ && _. fa 1.
    rewrite -(if_true (Setup(pid) <= pred t) _ zero) in 1 => //.
    by apply  Hind (pred(t)).
Qed.


(*------------------------------------------------------------------*)
abstract tmax : timestamp.

axiom [any] max_ts :
  happens(tmax) &&
  (forall (t : timestamp), happens(t) => t <= tmax).

hint smt max_ts.

global lemma equiv_real_ideal_enrich_tmax0 :
  ([happens(tmax)] /\
   [forall (t' : timestamp), happens(t') => t' <= tmax] /\
    equiv(
     frame@tmax,
     seq(t':timestamp => if t' <= tmax then exec@t' else false),
     seq(i:index, t':timestamp => if t' <= tmax then YCtr(i)@t'),
     seq(i:index, t':timestamp => if t' <= tmax then SCtr(i)@t')
  )).
Proof.
  use max_ts as [_ U].
  split; 1: auto.
  split.
    + smt  ~steps:23677. 
    + by apply ~inductive equiv_real_ideal_enrich tmax.
Qed.

axiom [any] sctr_nhap (i : index, t' : timestamp) :
   not (happens(t')) => SCtr(i)@t' = empty.

axiom [any] yctr_nhap (i : index, t' : timestamp) :
   not (happens(t')) => YCtr(i)@t' = empty.

hint smt sctr_nhap.
hint smt yctr_nhap.

(* default value of `exec` at timestamp not in the trace. Left arbitrary. *)
abstract exec_dflt : boolean.

axiom [any] exec_nhap (t' : timestamp) :
   not (happens(t')) => exec@t' = exec_dflt.

hint smt exec_nhap.

global lemma equiv_real_ideal_enrich_tmax :
  ([happens(tmax)] /\
   [forall (t' : timestamp), happens(t') => t' <= tmax] /\
    equiv(
      frame@tmax,
      seq(t':timestamp => exec@t'),
      seq(i:index, t':timestamp => YCtr(i)@t'),
      seq(i:index, t':timestamp => SCtr(i)@t')
  )).
Proof.
  use equiv_real_ideal_enrich_tmax0 as [Hap C U].
  split; 1: auto.
  split; 1: auto.
  assert (forall (t' : timestamp), (t' <= tmax) = happens(t')) as Eq. smt  ~steps:24873.
  rewrite !Eq in U.

  splitseq 3: (fun (i : index, t' : timestamp) => happens(t')).
  splitseq 2: (fun (i : index, t' : timestamp) => happens(t')).
  splitseq 1: (fun (t' : timestamp) => happens(t')).
  simpl.

  constseq 6 :
    (fun (i : index, t' : timestamp) => happens(t')) zero
    (fun (i : index, t' : timestamp) => not (happens(t'))) empty. 
    + simpl; smt  ~steps:22777.
    + simpl. smt  ~steps:24213.   

    + constseq 4 :
      (fun (i : index, t' : timestamp) => happens(t')) zero
      (fun (i : index, t' : timestamp) => not (happens(t'))) empty.
        - simpl; smt  ~steps:22777.
        - simpl; smt  ~steps:24213.
       - constseq 2 :
        (fun (t' : timestamp) => happens(t')) false
        (fun (t' : timestamp) => not (happens(t'))) exec_dflt.
          * simpl;smt  ~steps:22777.
          * simpl;smt  ~steps:24902.
          * by apply U.
Qed.

(*------------------------------------------------------------------*)
global lemma injective_correspondence_equiv (pid, j:index[const]):
   [happens(Server(pid,j))] ->
   equiv(
     exec@Server(pid,j) =>
     exists (i:index),
       Press(pid,i) < Server(pid,j) &&
       YCtr(pid)@pred(Press(pid,i)) = SCtr(pid)@Server(pid,j) &&
       forall (j':index), happens(Server(pid,j')) =>
         exec@Server(pid,j') =>
         YCtr(pid)@pred(Press(pid,i)) = SCtr(pid)@Server(pid,j') =>
         j = j').
Proof.
  intro Hap.
  use equiv_real_ideal_enrich_tmax as [_ _ H].
  apply H.
Qed.

(*------------------------------------------------------------------*)
(* The final proof of injective correspondence. *)
lemma [default/left] injective_correspondence (j, pid:index[glob]):
   happens(Server(pid,j)) =>
   exec@Server(pid,j) =>
     exists (i:index),
       Press(pid,i) < Server(pid,j) &&
       YCtr(pid)@pred(Press(pid,i)) = SCtr(pid)@Server(pid,j) &&
       forall (j':index), happens(Server(pid,j')) =>
         exec@Server(pid,j') =>
         YCtr(pid)@pred(Press(pid,i)) = SCtr(pid)@Server(pid,j') =>
         j = j'.
Proof.
  intro Hap.
  rewrite equiv injective_correspondence_equiv pid j => // Hexec.
  expand exec, cond.
  destruct Hexec as [Hexecpred Mneq1 Mneq2 Hcpt Hpid].
  expand deccipher.
  intctxt Mneq2 => //.
  intro [j0 [Ht Eq]].
  exists j0 => /=.
  split => //.

  intro j' Hap' Hexec'.
  use counterIncreaseBis as HH. 
  assert (Server(pid,j) = Server(pid,j') || Server(pid,j) < Server(pid,j') || Server(pid,j) > Server(pid,j')) as H => //. smt ~prover:CVC5_stringscounterexamples ~steps:394268.
Qed.
