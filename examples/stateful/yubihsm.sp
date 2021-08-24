(*******************************************************************************
YUBIHSM

[1] R. Künnemann, "Foundations for analyzing security APIs in the symbolic and
computational model", 2014.

Y   -> S   : <pid,<nonce,otp>>
S   -> HSM : <pid,kh>,<aead,otp>>
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

- The last message "otp || nonce || hmac || status" is unclear and not modelled
at all and replaced by "accept".
It was also not modelled in [1].

- The otp is an encryption of a triple (sid, ctr, npr).
It is modelled here as a randomized encryption of a pair (sid, ctr).

- enc is assumed to be AEAD (we do not use the associated data)

- In [1], they "over-approximate in the case that the Yubikey increases the
session token by allowing the adversary to instantiate the rule for any counter
value that is higher than the previous one".
Here, we model the incrementation by 1 of the counter.

- As in [1], we model the two counters (session and token counters) as a single
counter.

- In [1], the server keeps in memory the mapping between public and
  secret identities of the Yubikeys. As far as we understand, this
  does not reflect the YubiHSM specification: secret identities are to
  be protected by the YubiHSM.  Instead, we choose to keep the
  necessary information to map public to private indentities in the
  AEADs (we simply add the public identity to the AEADs plaintext).  

- Diff terms are here to model a real system and two ideal systems.
  - the first intermediate ideal system replace key look-up in the 
    server database by the honest keys;
  - the fully ideal system uses a different key k2'(i,j) for each 
    generated otp. The goal is to being able to use the intctxt tactic for 
    the auth goal.
*******************************************************************************)
set autoIntro=false.

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

(* Order over counters.
   Assumed transitive and strict later through axioms. *)
abstract (~<): message -> message -> boolean.

(* When the key is plugged for yubikey `pid`, the counter is incremented. *)
process yubikeyplug (pid:index) =
  in(cY,x1);
  YCtr(pid) := mySucc(YCtr(pid));
  out(cY,endplug).

name nonce : index -> index -> message
name npr : index -> index -> message

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
   - it checks that the counter inside the otp (received from the HSM) is strictly
   greater than the counter associated to the token,
   - if so, this counter value is used to update the database.

   In our modelling, the server request to the HSM (to retrieve k(pid) 
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
(* base system with ideal system *)
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


(* TODO: allow to have axioms for all systems *)
axiom orderTrans (n1,n2,n3:message): n1 ~< n2 => n2 ~< n3 => n1 ~< n3.

axiom orderStrict(n1,n2:message): n1 = n2 => n1 ~< n2 => False.

axiom mpid_inj (pid, pid':index): mpid(pid) = mpid(pid') => pid = pid'.

axiom pair_ne_fail (x,y: message) : <x,y> <> fail.

(* LIBRAIRIES *)

axiom eq_iff (x, y : boolean) : (x = y) = (x <=> y).

goal eq_refl ['a] (x : 'a) : (x = x) = true. 
Proof. print.
  by rewrite eq_iff. 
Qed.
hint rewrite eq_refl.

goal eq_sym ['a] (x,y : 'a) : x = y => y = x.
Proof. auto. Qed.

(* SP: merge with eq_refl *)
goal eq_refl_i (x : index) : (x = x) = true.
Proof.
  by rewrite eq_iff. 
Qed.
hint rewrite eq_refl_i.

(* SP: merge with eq_refl *)
goal eq_refl_t (x : timestamp) : (x = x) = true.
Proof.
  by rewrite eq_iff. 
Qed.
hint rewrite eq_refl_t.


axiom not_true : not(true) = false.
hint rewrite not_true.

axiom not_false : not(false) = true.
hint rewrite not_false.

(* new *)
axiom true_false : (true = false) = false.
hint rewrite true_false.

(* new *)
goal false_true : (false = true) = false.
Proof. 
  (* TODO: work-around until we have a better type inference *)
  (* rewrite (eq_sym false true). *)
  assert (forall (x,y : boolean), (x = y) = (y = x)) as H .
    intro _ _. 
    by rewrite eq_iff. 
  rewrite (H false true).
  auto.
Qed.
hint rewrite false_true.

goal not_not (b : boolean): not (not b) = b. 
Proof.
  by case b.
Qed.
hint rewrite not_not.

goal not_eq ['a] (x, y : 'a): not (x = y) = (x <> y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_eq.

(* new *)
goal not_eq_i (x, y : index): not (x = y) = (x <> y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_eq_i.

(* new *)
goal not_eq_t (x, y : timestamp): not (x = y) = (x <> y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_eq_t.

goal not_neq ['a] (x, y : 'a): not (x <> y) = (x = y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_neq.

(* new *)
goal not_neq_i (x, y : index): not (x <> y) = (x = y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_neq_i.

(* new *)
goal not_neq_t (x, y : timestamp): not (x <> y) = (x = y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_neq_t.

(* new *)
goal eq_false ['a] (x, y : 'a): ((x = y) = false) = (x <> y).
Proof. 
rewrite -not_eq. case (x = y) => _. simpl. auto.
by rewrite eq_iff. 
Qed.
hint rewrite eq_false.

(* new *)
goal eq_false_i (x, y : index): ((x = y) = false) = (x <> y).
Proof. 
rewrite -not_eq_i. case (x = y) => _. simpl. auto.
by rewrite eq_iff. 
Qed.
hint rewrite eq_false_i.

(* new *)
goal eq_false_t (x, y : timestamp): ((x = y) = false) = (x <> y).
Proof. 
rewrite -not_eq_t. case (x = y) => _. simpl. auto.
by rewrite eq_iff. 
Qed.
hint rewrite eq_false_t.

(*------------------------------------------------------------------*)
(* and *)

axiom and_comm (b,b' : boolean) : (b && b') = (b' && b).

axiom and_true_l (b : boolean) : (true && b) = b.
hint rewrite and_true_l.

goal and_true_r (b : boolean) : (b && true) = b.
Proof. by rewrite and_comm and_true_l. Qed.
hint rewrite and_true_r.

axiom and_false_l (b : boolean) : (false && b) = false.
hint rewrite and_false_l.

goal and_false_r (b : boolean) : (b && false) = false.
Proof. by rewrite and_comm and_false_l. Qed.
hint rewrite and_false_r.

(*------------------------------------------------------------------*)
(* or *)
axiom or_comm (b,b' : boolean) : (b || b') = (b' || b).

axiom or_false_l (b : boolean) : (false || b) = b.
hint rewrite or_false_l.

goal or_false_r (b : boolean) : (b || false) = b.
Proof. by rewrite or_comm or_false_l. Qed.
hint rewrite or_false_r.

axiom or_true_l (b : boolean) : (true || b) = true.
hint rewrite or_true_l.

goal or_true_r (b : boolean) : (b || true) = true.
Proof. by rewrite or_comm or_true_l. Qed.
hint rewrite or_true_r.

(*------------------------------------------------------------------*)
(* if *)

goal if_true ['a] (b : boolean, x,y : 'a):
 b => if b then x else y = x.
Proof.
  by intro *; yesif.
Qed.

goal if_true0 ['a] (x,y : 'a):
 if true then x else y = x.
Proof.
  by rewrite if_true. 
Qed.
hint rewrite if_true0.

goal if_false ['a] (b : boolean, x,y : 'a):
 (not b) => if b then x else y = y.
Proof.
  by intro *; noif.
Qed.

goal if_false0 ['a] (x,y : 'a):
 if false then x else y = y.
Proof.
  by rewrite if_false.
Qed.
hint rewrite if_false0.

goal if_then_then ['a] (b,b' : boolean, x,y : 'a):
  if b then (if b' then x else y) else y = if (b && b') then x else y.
Proof.  
  by case b; case b'.
Qed.

goal if_same ['a] (b : boolean, x : 'a):
  if b then x else x = x.
Proof.
  by case b.
Qed.
hint rewrite if_same.

(* new *)
goal if_then ['a] (b,b' : boolean, x,y,z : 'a):
 b = b' => 
 if b then (if b' then x else y) else z = 
 if b then x else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_then.

(* new *)
goal if_else ['a] (b,b' : boolean, x,y,z : 'a):
 b = b' => 
 if b then x else (if b' then y else z) = 
 if b then x else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_else.

(* new *)
goal if_then_not ['a] (b,b' : boolean, x,y,z : 'a):
 b = not b' => 
 if b then (if b' then x else y) else z = 
 if b then y else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_then_not.

(* new *)
goal if_else_not ['a] (b,b' : boolean, x,y,z : 'a):
  b = not b' => 
 if b then x else (if b' then y else z) = 
 if b then x else y.
Proof.  
  by intro ->; case b'.
Qed.
hint rewrite if_else_not.

(*------------------------------------------------------------------*)
(* new *)
goal dec_enc (x,r,k : message): dec(enc(x,r,k),k) = x.
Proof. auto. Qed.
hint rewrite dec_enc.

goal fst_pair (x,y : message) : fst (<x,y>) = x.
Proof. auto. Qed.
hint rewrite fst_pair.

goal snd_pair (x,y : message) : snd (<x,y>) = y.
Proof. auto. Qed.
hint rewrite snd_pair.

goal diff_eq ['a] (x,y : 'a) : x = y => diff(x,y) = x.
Proof. by project. Qed.
hint rewrite diff_eq.

goal diff_diff_l ['a] (x,y,z: 'a): diff(diff(x,y),z) = diff(x,z).
Proof. by project. Qed.
hint rewrite diff_diff_l.

goal diff_diff_r ['a] (x,y,z: 'a): diff(x,diff(y,z)) = diff(x,z).
Proof. by project. Qed.
hint rewrite diff_diff_r.

(* instances of f_apply *)
goal dec_apply (x,x',k : message): x = x' => dec(x,k) = dec(x',k).
Proof. auto. Qed.

(* Others *)

goal le_pred_lt (t, t' : timestamp): (t <= pred(t')) = (t < t').
Proof. 
  by rewrite eq_iff.
Qed.

goal le_not_lt (t, t' : timestamp): 
  t <= t' => not (t < t') => t = t'.
Proof.
  by case t' = init. 
Qed.

goal le_not_lt_charac (t, t' : timestamp):
 (not (t < t') && t <= t') = (happens(t) && t = t').
Proof.
 by rewrite eq_iff.
Qed.

goal lt_impl_le (t, t' : timestamp): 
  t < t' => t <= t'.
Proof. auto. Qed.

goal le_lt (t, t' : timestamp): 
  t <> t' => (t <= t') = (t < t').
Proof. 
  by intro *; rewrite eq_iff. 
Qed.


(* PROOF *)

(* First property of AEAD decoding *)
goal valid_decode (t : timestamp) (pid,j : index):
  (t = Decode(pid,j) || t = Decode1(pid,j)) =>
  happens(t) => 
  (aead_dec(pid,j)@t <> fail) =
  (exists(pid0 : index), 
   Setup(pid0) < t &&
   AEAD(pid0)@Setup(pid0) = aead(pid,j)@t).
Proof.
  intro Eq Hap.
  rewrite eq_iff; split.

  (* Left => Right *)
  intro AEAD_dec.

  case Eq; 
  expand aead_dec;
  intctxt AEAD_dec => H //;
  intro AEAD_eq;
  by exists pid0. 

  (* Right => Left *) 
  intro [pid0 [Clt H]].
  case Eq; 
  expand aead_dec;
  rewrite -H /AEAD /=;
  apply pair_ne_fail.
Qed.  

(* using the `valid_decode` lemma, we can characterize when the full
   decoding check goes through *)
goal valid_decode_charac (t : timestamp) (pid,j : index):
  (t = Decode(pid,j) || t = Decode1(pid,j)) =>
  happens(t) => 
  ( aead_dec(pid,j)@t <> fail &&
    otp_dec(pid,j)@t <> fail &&
    fst(otp_dec(pid,j)@t) = snd(snd(aead_dec(pid,j)@t)) &&
    mpid(pid) = fst(snd(aead_dec(pid,j)@t)) ) 
  =
  ( AEAD(pid)@Setup(pid) = aead(pid,j)@t &&
    dec(otp(pid,j)@t,k(pid)) <> fail &&
    fst(dec(otp(pid,j)@t,k(pid))) = sid(pid) ).
Proof.
  intro Eq Hap.
  rewrite eq_iff; split.

  (* => case *)
  intro [AEAD_dec OTP_dec Sid_eq Pid_eq]. 
  rewrite valid_decode // in AEAD_dec.
  destruct AEAD_dec as [pid0 [Clt AEAD_dec]]. 
  
  assert (pid0 = pid).
  by case Eq; use mpid_inj with pid, pid0.
  case Eq; project; auto.

  (* <= case *)
  intro [AEAD_dec OTP_dec Sid_eq].
  rewrite valid_decode //. 
  case Eq;
  depends Setup(pid), t by auto;
  intro Clt;
  by project; simpl; exists pid.
Qed.


(*------------------------------------------------------------------*)
(* auxilliary simple lemma, used to rewrite one of the conditional
   equality in the then branch. *)
goal if_aux (b,b0,b1,b2 : boolean) (x,y,z,u,v:message):
   if (b && (x = y && b0 && b1 && b2)) then
     snd(dec(z,diff(fst(dec(y,u)),v))) =
   if (b && (x = y && b0 && b1 && b2)) then 
    snd(dec(z,diff(fst(dec(x,u)),v))). 
Proof.
  intro >. 
  case b => _ //. 
  case b0 => _ //. 
  case b1 => _ //.
  case b2 => _ //. 
  case (x = y) => U //.
Qed.

(*------------------------------------------------------------------*)
(* set showStrengthenedHyp=true. *)
equiv atomic_keys.
Proof.
  enrich seq(pid,j:index -> npr(pid,j)). 
  enrich seq(pid,j:index -> nonce(pid,j)). 
  enrich seq(pid:index -> k(pid)).
  enrich seq(pid:index -> k_dummy(pid)).
  enrich seq(pid:index -> sid(pid)).
  enrich seq(pid:index -> if Setup(pid) <= t then AEAD(pid)@Setup(pid)).
  enrich seq(pid:index -> AEAD(pid)@t).

  dependent induction t => t Hind Hap.
  case t => Eq;
  try (
    repeat destruct Eq as [_ Eq];
    (rewrite le_lt; 1:auto);
    rewrite !-le_pred_lt;
    expandall;
    by apply Hind (pred(t))).

  (* init *)
  rewrite /*. 
  constseq 1: zero; 1: by rewrite if_false. 
  auto.

  (* Setup *)
  repeat destruct Eq as [_ Eq]. 
  rewrite /* in 7.
  splitseq 1: (fun (pid : index) -> Setup(pid) < t).
  rewrite !if_then_then in 1,2.

  assert (forall (t, t' : timestamp), 
   (t < t' && t <= t') = (t < t')) as lt_le_eq_lt.
  by rewrite eq_iff.
  rewrite lt_le_eq_lt in 1.

  (* le_not_lt_charac *)
  rewrite le_not_lt_charac in 2.

  constseq 2: (AEAD(pid)@t) zero. 
    intro pid0.
    case pid0 = pid => _; 
      [1: by left; rewrite if_true |
       2: by right; by rewrite if_false].
  
  rewrite !-le_pred_lt.
  by apply Hind (pred(t)).

  (* Write(pid,j) *)
  repeat destruct Eq as [_ Eq]. 
  rewrite le_lt; 1:auto.
  rewrite !-le_pred_lt.
  rewrite /* in 7.
  by apply Hind (pred(t)).

  (* Decode(pid,j) *)
  repeat destruct Eq as [_ Eq].
  rewrite le_lt; 1:auto.
  rewrite !-le_pred_lt.
  depends Setup(pid), t by auto => H.
  rewrite /frame /exec /output /cond in 7. 
  fa 7; fa 8; fa 8.

  rewrite valid_decode_charac //. 
  (* rewrite the content of the then branch *)
  rewrite /otp_dec /aead_dec if_aux /= in 9.
  fa 9.
  rewrite /AEAD /= in 9.
  rewrite /aead /otp in 8,9.
  by apply Hind (pred(t)).

  (* Decode1(pid,j) *)
  repeat destruct Eq as [_ Eq].
  rewrite le_lt; 1:auto.
  rewrite !-le_pred_lt.
  depends Setup(pid), t by auto => H.
  rewrite /frame /exec /output /cond in 7. 
  fa 7; fa 8; fa 8.
  rewrite valid_decode_charac //. 
  rewrite /otp /aead.
  by apply Hind (pred(t)).
Qed.
  

(* The counter SCtr(j) strictly increases when t is an action Server performed by 
the server with tag j. *)

goal [right] counterIncreaseStrictly (pid,j:index):
   happens(Server(pid,j)) =>
   cond@Server(pid,j) => 
   SCtr(pid)@pred(Server(pid,j)) ~< SCtr(pid)@Server(pid,j).
Proof.
auto.
Qed.

goal [right] counterIncrease (t:timestamp, pid : index) :
  happens(t) =>
  t > init && exec@t =>
    SCtr(pid)@pred(t) ~< SCtr(pid)@t ||
    SCtr(pid)@t = SCtr(pid)@pred(t).
Proof.
  intro Hap [Ht Hexec].
  case t;
  try (intro *; by right).

  intro [pid0 j0 E].
  case (pid = pid0) => Eq; 1: by left.

  by right; expand SCtr; noif.
Qed.


(* The counter SCpt(ped) increases (not strictly) between t' and t when t' < t *)
goal [right] counterIncreaseBis:
  forall (t:timestamp), forall (t':timestamp), forall (pid:index),
    happens(t) =>
    exec@t && t' < t =>
    ( SCtr(pid)@t' ~< SCtr(pid)@t || 
      SCtr(pid)@t = SCtr(pid)@t').
Proof.
  induction.
  intro t IH0 t' pid Hap [Hexec Ht'].
  assert (t' = pred(t) || t' < pred(t)) as H0; 
  1: case t; constraints. 
  case H0.

  (* case t' = pred(t) *)
  rewrite !H0. 

  by apply counterIncrease.

  (* case t' < pred(t) *)
  use IH0 with pred(t),t',pid as H1 => //=.
  use counterIncrease with t,pid as H3 => //.
  case H1 => //.
    (* case H1 - 1/2 *)
    case H3 => //.
      by left; apply orderTrans _ (SCtr(pid)@pred(t)) _.
      (* case H1 - 2/2 *)
      left. 
      by rewrite -H3 in H1.

    case H3 => //=. 
    left.
    by rewrite H1 in H3.
    
    by right.

  executable t => // H1. 
  by apply H1.
Qed.


(* Property 1 - No replay relying on an invariant *)

goal [right] noreplayInv (j, j', pid:index):
   happens(Server(pid,j),Server(pid,j')) =>
   exec@Server(pid,j') && Server(pid,j) < Server(pid,j') => 
   SCtr(pid)@Server(pid,j) ~< SCtr(pid)@Server(pid,j').
Proof.
  intro Hap [Hexec Ht].
  use counterIncreaseStrictly  with pid, j' as H0 => //.
  assert (Server(pid,j) = pred(Server(pid,j')) ||
          Server(pid,j) < pred(Server(pid,j'))) as H1
  by constraints.
  case H1.

  (* case Server(pid,j) = pred(Server(pid,j')) *)
  by rewrite H1 in *.

  (* case Server(pid,j) < pred(Server(pid,j')) *)
  use counterIncreaseBis with pred(Server(pid,j')),Server(pid,j),pid as H2 => //.
  case H2; 
  1: by apply orderTrans _ (SCtr(pid)@pred(Server(pid,j'))) _.

  by rewrite H2 in *.
Qed.


goal [right] noreplay (j, j', pid:index):
  happens(Server(pid,j')) =>
  exec@Server(pid,j') =>
  Server(pid,j) <= Server(pid,j') =>
  SCtr(pid)@Server(pid,j)= SCtr(pid)@Server(pid,j')=> 
  j = j'.
Proof.
  intro Hap Hexec Ht Meq.
  assert (Server(pid,j) = Server(pid,j') ||
          Server(pid,j) < Server(pid,j')) as H1 
  by constraints.
  case H1 => //.

  use noreplayInv with j, j', pid as M1 => //. 
  by apply orderStrict in Meq.
Qed.


(* Property 3 *)
(* Monotonicity *)

goal [right] monotonicity (j, j', pid:index):
  happens(Server(pid,j'),Server(pid,j)) =>
  exec@Server(pid,j') && exec@Server(pid,j) && 
  SCtr(pid)@Server(pid,j) ~< SCtr(pid)@Server(pid,j') =>
  Server(pid,j) < Server(pid,j').
Proof.
  intro Hap [Hexec H].
  assert
    (Server(pid,j) = Server(pid,j') || 
     Server(pid,j)< Server(pid,j') || 
     Server(pid,j) > Server(pid,j')) as Ht;
  1: constraints.
  case Ht.

  (* case Server(pid,j) = Server(pid,j') *)
  by apply orderStrict in H.

  (* case Server(pid,j) < Server(pid,j') *)
  assumption.

  (* case Server(pid,j) > Server(pid,j') *)
  use noreplayInv with j', j, pid  as Meq => //.
  (* apply orderTrans _ (SCtr(pid)@Server(pid,j')) in H => //. *)
  use orderTrans with 
      SCtr(pid)@Server(pid,j),
      SCtr(pid)@Server(pid,j'), 
      SCtr(pid)@Server(pid,j) => //.
  by apply orderStrict in H0.
Qed.



(* Property 2 *)
(* injective correspondance as stated in the PhD thesis of R. Kunneman *)

goal [right] injective_correspondance (j, pid:index):
   happens(Server(pid,j)) =>
   exec@Server(pid,j) =>
     exists (i:index),
       Press(pid,i) < Server(pid,j) && 
       ctr(pid,i)@Press(pid,i) = SCtr(pid)@Server(pid,j) && 
       forall (j':index), happens(Server(pid,j')) =>
         exec@Server(pid,j') =>
         ctr(pid,i)@Press(pid,i) = SCtr(pid)@Server(pid,j') => 
         j = j'.

Proof.
intro Hap Hexec.
executable Server(pid,j) => //.
intro exec.
expand exec, cond.
destruct Hexec as [Hexecpred [[Mneq1 Mneq2] Hcpt Hpid]].
expand deccipher.
intctxt Mneq2 => //.   

intro Ht M1 Eq.
exists j0.
split => //. 


intro j' Hap' Hexec'. 

intro Eq => //.  
assert (SCtr(pid)@Server(pid,j) = SCtr(pid)@Server(pid,j')) as Meq by auto.

assert (Server(pid,j) = Server(pid,j') || 
        Server(pid,j) < Server(pid,j') || 
        Server(pid,j) > Server(pid,j')) => //. 
case H => //. 

(* 1st case: Server(pid,j) < Server(pid,j') *) 
assert (Server(pid,j) = pred(Server(pid,j')) || 
        Server(pid,j) < pred(Server(pid,j'))) by constraints.
case H0 => //. 


(* Server(pid,j) = pred(Server(pid,j') < Server(pid,j') *)
use counterIncreaseStrictly with pid, j' => //.
rewrite H0 in *.
by apply orderStrict in Meq.

(* Server(pid,j) < pred(Server(pid,j'))  < Server(pid,j') *) 
use counterIncreaseStrictly with pid, j' => //. 
use counterIncreaseBis with pred(Server(pid,j')), Server(pid,j), pid => //. 
case H2.

use orderTrans with 
   SCtr(pid)@Server(pid,j), 
   SCtr(pid)@pred(Server(pid,j')), 
   SCtr(pid)@Server(pid,j') => //.
by apply orderStrict in Meq.

rewrite H2 in *. 
by apply orderStrict in Meq.

(* 2nd case: Server(pid,j) > Server(pid,j')  *)
assert (pred(Server(pid,j)) = Server(pid,j') 
        || pred(Server(pid,j)) > Server(pid,j')) by constraints.
case H0 => //. 

(* Server(pid,j) > pred(Server(pid,j)) = Server(pid,j') *)
use counterIncreaseStrictly with pid, j as H1 => //.
by apply orderStrict in H1.

(* Server(pid,j)  > pred(Server(pid,j)) >  Server(pid,j') *) 
use counterIncreaseStrictly with pid, j => //.
use counterIncreaseBis with pred(Server(pid,j)), Server(pid,j'), pid  => //. 
case H2. 

apply orderTrans _ _ (SCtr(pid)@Server(pid,j)) in H2; 1: auto.
apply eq_sym in Meq. 
by apply orderStrict in Meq.

by apply orderStrict in H1.
Qed.
