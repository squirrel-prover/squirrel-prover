(*******************************************************************************
YUBIHSM

[1] R. Künnemann, "Foundations for analyzing security APIs in the symbolic and
computational model", 2014.

Y   -> S   : <pid,<nonce,otp>>
S   -> HSM : <pid,kh>,<aead,otp>>
HSM -> S   : ctr
S   -> Y   : accept

with
- aead = senc(<k,sid>,mkey)
- otp = senc(<sid,ctr>,npr,k)

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

- senc is assumed to be AEAD (we do not use the associated data)

- In [1], they "over-approximate in the case that the Yubikey increases the
session token by allowing the adversary to instantiate the rule for any counter
value that is higher than the previous one".
Here, we model the incrementation by 1 of the counter.

- As in [1], we model the two counters (session and token counters) as a single
counter.

- Diff terms are here to model a real system and two ideal systems.
  - the first intermediate ideal system replace key look-up in the 
    server database by the honest keys;
  - the fully ideal system uses a different key k2'(i,j) for each 
    generated otp. The goal is to being able to use the intctxt tactic for 
    the auth goal.
*******************************************************************************)
set autoIntro=false.

senc enc,dec

abstract startplug: message
abstract endplug: message
abstract startpress: message
abstract accept:message

(* counters initial value *)
abstract cinit : message
(* counter successor *)
abstract mySucc : message -> message

(* encoding of a public identity as a message *)
abstract mpid: index -> message

(* secret identity *)
name sid: index -> message

(* public key handle kh to reference the AES master key mkey *)
abstract kh: message
name mkey: message

(* working key k(pid) of yubikey `pid`, stored inside the AEAD *)
name k: index -> message
(* Dummy key used in AEAD idealized so that the key does not occur in 
   plaintext anymore in the idealized system *)
name k_dummy: index -> message

(* counters *)
mutable YCtr(i:index) : message = cinit
mutable SCtr(i:index) : message = cinit

(* random samplings used to initialized AEAD  *)
name rinit : index -> message
(* authentication server's database for each pid *)
mutable AEAD(pid:index) : message = 
  enc(<diff(k(pid),k_dummy(pid)), sid(pid)>, rinit(pid), mkey).

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

(* fully idealized version of `yubikeypress`. *)
(* process yubikeypress_ideal (pid:index,j:index) =
  in(cY,x2);  
  let ctr = YCtr(pid) in
  YCtr(pid) := mySucc(YCtr(pid));
  let menc = enc(<sid(pid),ctr>,npr(pid,j),diff(k(pid),k'(pid,j))) in
  out(cY,<mpid(pid), <nonce(pid,j), menc>>).
*)

(* When the server receives a message for pid:
   - it checks whether it corresponds to a pid in its database,
   - it retrieves the AEAD and kh associated to this pid and asks the HSM to
   decode the received otp,
   - it checks that the counter inside the otp (received from the HSM) is strictly
   greater than the counter associated to the token,
   - if so, this counter value is used to update the database.
In this modelling, the server role does not ask anything to the HSM.
 *)
process server (pid:index) =
  in(cS,x); (*x = <pid,<nonce, cipher>> with cipher = senc(<sid,cpt>,r, k)*)
  let cipher = snd(snd(x)) in
  let deccipher = dec(cipher,k(pid)) in
  let xcpt = snd(deccipher) in
  if fst(x) = mpid(pid) 
  && deccipher<>fail && fst(deccipher) = sid(pid) && SCtr(pid) ~< xcpt then
  SCtr(pid) := xcpt;
  out(cS,accept).

(*
process server_ideal(pid,j:index) = 
  in(cS,x); (*x = <pid,<nonce, cipher>> with cipher = senc(<sid,cpt>,r, k)*)
  let cipher = snd(snd(x)) in
  let deccipher = dec(cipher,k(pid)) in
  let xcpt = snd(deccipher) in 
  if fst(x) = mpid(pid) &&  
    diff(SCtr(pid) ~< xcpt  &&deccipher<>fail && fst(deccipher) = sid(pid), 
exists (j':index), dec(cipher,k'(pid,j')) <> fail && fst(dec(cipher,k'(pid,j'))) = sid(pid) && SCtr(pid) ~< snd(dec(cipher,k'(pid,j'))))  
 then
  SCtr(pid) := diff(xcpt, try find j' such that dec(cipher,k'(pid,j')) <> fail && fst(dec(cipher,k'(pid,j'))) = sid(pid) in snd(dec(cipher,k'(pid,j'))));
  out(cS,accept).
*)


(* The attacker can read/write AEAD stored in the server's database. *)
process read_AEAD (pid:index) =
  out(cS,AEAD(pid)).

process write_AEAD (pid:index)=
  in(cS,x);
  AEAD(pid) := x.

(* Model for the rule YSM_AEAD_YUBIKEY_OTP_DECODE of the HSM. *)
process YSM_AEAD_YUBIKEY_OTP_DECODE (pid:index) =
  in(cHSM,xdata); (* xdata = <<pid,kh>, <aead, otp>> with otp = senc(<sid,cpt>,r,k)*)
   if fst(xdata) = <mpid(pid),kh> then
    let aead = fst(snd(xdata)) in
    let otp = snd(snd(xdata)) in

    let aead_dec = dec(aead,mkey) in    
    let sid_pid = diff(snd(aead_dec), sid(pid)) in

    let otp_dec = dec(otp,diff(fst(aead_dec), k(pid))) in

    if aead_dec <> fail && otp_dec <> fail && fst(otp_dec) = sid_pid
    then
      out(cHSM, snd(otp_dec)).

(* fully idealized version of `YSM_AEAD_YUBIKEY_OTP_DECODE`. *)
(* process YSM_AEAD_YUBIKEY_OTP_DECODE_ideal (pid:index) =
  in(cHSM,xdata);
  if fst(xdata) = <mpid(pid),kh> then
    let aead = fst(snd(xdata)) in
    let otp = snd(snd(xdata)) in

    let aead_dec = dec(aead,mkey) in    
    let otp_dec = dec(otp,k(pid)) in

    if aead_dec <> fail && 
       diff( otp_dec <> fail && fst(otp_dec) = sid(pid),
             exists (j:index),
             dec(otp,k'(pid,j)) <> fail &&
             fst(dec(otp,k'(pid,j))) = sid(pid))
    then
      out(cHSM, 
          diff( snd(otp_dec),
                try find j such that 
                  dec(otp,k'(pid,j)) <> fail && 
                  fst(dec(otp,k'(pid,j))) = sid(pid)
                in
                snd(dec(otp,k'(pid,j))))).
*)

(* base system with middle system *)
 system (* [BtoM] *)
  ( (!_pid !_j Plug   : yubikeyplug(pid)                 ) |
    (!_pid !_j Press  : yubikeypress(pid,j)              ) |
    (!_pid !_j Server : server(pid)                      ) |
    (!_pid !_j Read   : read_AEAD(pid)                   ) |
    (!_pid !_j Write  : write_AEAD(pid)                  ) | 
    (!_pid !_j Decode : YSM_AEAD_YUBIKEY_OTP_DECODE(pid) )).


(* middle system with ideal system *)
(* system (* [MtoI] *)
  ( (!_pid !_j Plug   : yubikeyplug(pid)                       ) |
    (!_pid !_j Press  : yubikeypress_ideal(pid,j)              ) |
    (!_pid !_j Server : server_ideal(pid,j)                            ) |
   (!_pid !_j Read   : read_AEAD(pid)                         ) |
    (!_pid !_j Write  : write_AEAD(pid)                        ) | 
    (!_pid !_j Decode : YSM_AEAD_YUBIKEY_OTP_DECODE_ideal(pid) )).
*)

(* TODO: allow to have axioms for all systems *)
axiom  orderTrans (n1,n2,n3:message): n1 ~< n2 => n2 ~< n3 => n1 ~< n3.

(* TODO: allow to have axioms for all systems *)
axiom  orderStrict(n1,n2:message): n1 = n2 => n1 ~< n2 => False.

(* LIBRAIRIES *)

axiom eq_iff (x, y : boolean) : (x = y) = (x <=> y).

goal eq_refl ['a] (x : 'a) : (x = x) = true. 
Proof.
  by rewrite eq_iff. 
Qed.
hint rewrite eq_refl.

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

(* PROOF *)

goal [left] valid_decode (t : timestamp) (pid,j : index):
  t = Decode(pid,j) =>
  happens(t) => 
  aead_dec(pid,j)@t <> fail && 
  otp_dec(pid,j)@t <> fail &&
  fst(otp_dec(pid,j)@t) = sid_pid(pid,j)@t && 
  fst(input@t) = <mpid(pid),kh> =>
  snd(otp_dec(pid,j)@t) = k(pid).
Proof.
  intro Eq Hap [AEAD_dec OTP_dec Sid_eq U].
  clear U.
  expand aead_dec.
  intctxt AEAD_dec => H; 2: congruence.

  clear H; intro AEAD_eq.
  rewrite /otp_dec /sid_pid /aead_dec -AEAD_eq /= in *.
  clear AEAD_dec. 
  
  (* TODO: to apply intctxt, we probably need an additional intermediate system *)
  admit.
  (* intctxt OTP_dec. *)
Qed.  

(* TODO: factorize both lemmas *)
goal [right] valid_decode_r (t : timestamp) (pid,j : index):
  t = Decode(pid,j) =>
  happens(t) => 
  aead_dec(pid,j)@t <> fail && 
  otp_dec(pid,j)@t <> fail &&
  fst(otp_dec(pid,j)@t) = sid_pid(pid,j)@t && 
  fst(input@t) = <mpid(pid),kh> =>
  snd(otp_dec(pid,j)@t) = k(pid).
Proof.
  intro Eq Hap [AEAD_dec OTP_dec Sid_eq U].
  clear U.
  expand aead_dec.
  intctxt AEAD_dec => H; 2: congruence.

  clear H; intro AEAD_eq.
  rewrite /otp_dec /sid_pid -AEAD_eq /= in *.
  clear AEAD_dec. 
  
  intctxt OTP_dec; 2:auto. 
  intro Hc EncEq _.
  rewrite -EncEq /=.
  admit.
  (* TODO: the conclusion of the lemma is not correct. *)
Qed.  

set showStrengthenedHyp=true.
equiv atomic_keys.
Proof.
  enrich seq(pid,j -> npr(pid,j)). 
  enrich seq(pid,j -> nonce(pid,j)). 
  enrich seq(pid -> k(pid)).
  enrich seq(pid -> k_dummy(pid)).
  enrich seq(pid -> sid(pid)).
  enrich seq(pid -> AEAD(pid)@t).
  dependent induction t => t Hind Hap.
  case t => Eq;
  try (
    repeat destruct Eq as [_ Eq];
    expandall;
    by apply Hind (pred(t))).

  (* init *)
  admit. (* need to prove that all AEADs are indistinguishable *)

  (* Write(pid,j) *)
  repeat destruct Eq as [_ Eq]. 
  expandall.
  fa 6; fa 7; fa 7. 
  
  (* TODO: faseq 0 would allow to conclude there *)
  splitseq 0: (fun (pid0:index) -> pid0 = pid); simpl.
  constseq 0: (input@t) zero. 
  by intro * /=; case (pid0 = pid). 

  (* TODO: almost done *)
  (* by apply Hind (pred(t)). *)
  admit.

  (* Decode(pid,j) *)
  repeat destruct Eq as [_ Eq].
  expand frame, exec, output, cond. 
  fa 6. fa 7. fa 7.

  (* by apply Hind (pred(t)). *)
  admit.


  (* Decode1(pid,j) *)
  repeat destruct Eq as [_ Eq]. 
  expandall.
  fa 6; fa 7; fa 7; fa 8; fa 8.

  (* by apply Hind (pred(t)). *)
  admit.
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
assert (SCtr(pid)@Server(pid,j) = SCtr(pid)@Server(pid,j')) by auto.

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
by use orderStrict with 
  SCtr(pid)@pred(Server(pid,j')), SCtr(pid)@Server(pid,j'). 


(* Server(pid,j) < pred(Server(pid,j'))  < Server(pid,j') *) 
use counterIncreaseStrictly with pid, j' => //. 
use counterIncreaseBis with pred(Server(pid,j')), Server(pid,j), pid => //. 
case H2.

use orderTrans with 
   SCtr(pid)@Server(pid,j), 
   SCtr(pid)@pred(Server(pid,j')), 
   SCtr(pid)@Server(pid,j') => //. 
by use orderStrict with SCtr(pid)@Server(pid,j), SCtr(pid)@Server(pid,j').

rewrite H2 in *. 
by use orderStrict with SCtr(pid)@Server(pid,j), SCtr(pid)@Server(pid,j').

(* 2nd case: Server(pid,j) > Server(pid,j')  *)
assert (pred(Server(pid,j)) = Server(pid,j') 
        || pred(Server(pid,j)) > Server(pid,j')) by constraints.
case H0 => //. 

(* Server(pid,j) > pred(Server(pid,j)) = Server(pid,j') *)
use counterIncreaseStrictly with pid, j => //.
subst Server(pid,j'), pred(Server(pid,j)).
by use orderStrict with SCtr(pid)@pred(Server(pid,j)), SCtr(pid)@Server(pid,j).

(* Server(pid,j)  > pred(Server(pid,j)) >  Server(pid,j') *) 
use counterIncreaseStrictly with pid, j => //.
use counterIncreaseBis with pred(Server(pid,j)), Server(pid,j'), pid  => //. 
case H2. 

use orderTrans with 
  SCtr(pid)@Server(pid,j'),  
  SCtr(pid)@pred(Server(pid,j)), 
  SCtr(pid)@Server(pid,j) => //. 
by use orderStrict with SCtr(pid)@Server(pid,j'), SCtr(pid)@Server(pid,j). 

rewrite H2 in *.
by use orderStrict with SCtr(pid)@Server(pid,j'), SCtr(pid)@Server(pid,j). 
Qed.
