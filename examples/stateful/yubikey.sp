(**
# YUBIKEY

The YubiKey is a simple physical authentication device with a unique button.
This device, manufactured by Yubico, allows users to securely authenticate to
their accounts by issuing a one-time password (OTP).

In its typical configuration, the YubiKey generates a random OTP by encrypting
a secret value and a counter.
This message is accepted by the server only if it decrypts under the correct
key to a valid secret value containing a counter whose value is larger than the
last value accepted by the server for that YubiKey.

In this model, we analyze the security of the protocol as described in [1],
assuming that the server remains secure.

Yubico assigns a key `k`, as well as a public and a secret identifier `pid, sid`
to each YubiKey. The counter `cpt` inside the YubiKey is incremented whenever the
YubiKey is plugged in, as well as when an OTP is generated, i.e. when the button
of the YubiKey is pressed. This OTP is obtained by encrypting the counter value
and the `sid` of the YubiKey with the key `k`.

* YubiKey -> Server : <pid,<nonce,senc(<sid,cpt>,npr,k)>>

Here, `npr` is the encryption randomness. The server accepts this message if it
decrypts with a legitimate key `k`, and leads to a valid secret value `sid`.
Lastly, the counter value obtained through decryption has to be larger than the
current value stored in the server database. After this exchange, the server
updates its counter with the value just received.

#### COMMENTS

* The OTP is an encryption of a triple `<sid, cpt, npr>`.
It is modelled here as a randomized encryption of a pair `<sid, cpt>`.
According to the specification in [1], AES is used.

* In [1], they "over-approximate in the case that the Yubikey increases the
session token by allowing the adversary to instantiate the rule for any counter
value that is higher than the previous one".
Here, we model the incrementation by 1 of the counter.

#### SECURITY PROPERTIES

The 3 security properties as stated in [1].

* Property 1: absence of replay attacks.
* Property 2: injective correspondence.
* Property 3: monotonicity.

[1] R. Künnemann, "Foundations for analyzing security APIs in the symbolic and
computational model’, 2014.*)

set timeout=12.

(** Public constants (`abstract`) and names used in the protocol. *)
abstract startplug  : message
abstract endplug    : message
abstract startpress : message
abstract accept     : message
abstract pid        : index -> message

name sid  : index -> message
name nonce: index * index -> message.

(**
Symmetric encryption scheme, using the secret key `k` (with index arity 1
so that each YubiKey is associated to a key) and the random `npr` (with index
arity 2 so that each session of a YubiKey uses a new random name).
*)
senc enc,dec
name k  : index -> message
name npr: index * index -> message.

(**
Public constants and public functions used to model counter values.
*)
abstract myzero  : message
abstract myone   : message
abstract mySucc  : message -> message
abstract orderOk : message
abstract (~<)    : message -> message -> message.

(**
Mutable cells for the YubiKey and the server, initialized with `myzero`.
*)

mutable YCpt(i:index): message = myzero
mutable SCpt(i:index): message = myzero.

(** Communication channels used in the protocol. *)
channel cT
channel cR.

(** When the key is plugged, its counter is incremented. *)
process yubikeyplug(i:index,j:index) =
  in(cT, x1);
  if x1 = startplug then
    YCpt(i) := mySucc(YCpt(i));
    out(cT,endplug).

(** When the key is pressed, an OTP is sent with the current value of the
counter and the counter is incremented. *)
process yubikeypress(i:index,j:index) =
  in(cT,x2);
  if x2 = startpress then
    let cpt = YCpt(i) in
    YCpt(i) := mySucc(YCpt(i));
    out(cT,<pid(i),<nonce(i,j),enc(<sid(i),cpt>,npr(i,j),k(i))>>).

(** When the server receives a message, it checks whether it corresponds
to a pid in its database, and checks also that the counter inside the OTP
is strictly greater than the counter associated to the token.
If so, the value inside the OTP is used to update the database.
Now, the counter value associated to this token is this new value. *)
process server(ii:index) =
  in(cR,y1);
  try find i such that fst(y1) = pid(i) in
    (if dec(snd(snd(y1)),k(i)) <> fail
        && SCpt(i) ~< snd(dec(snd(snd(y1)),k(i))) = orderOk
    then
      SCpt(i) := snd(dec(snd(snd(y1)),k(i)));
      out(cR,accept)).

(** In the final system, processes can play in parallel an unbounded number
of sessions. *)
system
  ((!_i !_j Plug: yubikeyplug(i,j))
    | (!_i !_j Press: yubikeypress(i,j))
    | (!_ii S: server(ii))).


(** #### LIBRARIES

We include here some libraries, useful to help the tool with automated
reasoning. *)

include Basic.

lemma [any] dec_enc (x,y,z:message) : dec(enc(x,z,y),y) = x.
Proof. auto. Qed.
hint rewrite dec_enc.

lemma [any]  fst_apply (x,y : message) : x = y => fst(x) = fst(y).
Proof. auto. Qed.

lemma [any]  snd_apply (x,y : message) : x = y => snd(x) = snd(y).
Proof. auto. Qed.

lemma dec_apply (x,y,x1,y1 : message) :
 x = y => x1 = y1 => dec(x,x1) = dec(y,y1).
Proof. auto. Qed.

(** #### AXIOMS

The following axioms are used to reason on counter values. *)

axiom orderTrans (n1,n2,n3:message):
  n1 ~< n2 = orderOk => n2 ~< n3 = orderOk => n1 ~< n3 = orderOk.

axiom orderStrict (n1,n2:message):
  n1 = n2 => n1 ~< n2 <> orderOk.

axiom orderSucc (n1,n2:message):
  n1 = n2 => n1 ~< mySucc(n2) = orderOk.

(** #### HELPING LEMMAS

We now prove some properties on the counter on the server side, used later
in the proofs of the security properties. 

******************************************************)

(** The counter `SCpt(i)` strictly increases at each action `S` performed
by the server with tag `i`. *)
lemma counterIncreaseStrictly (ii,i:index):
  happens(S(ii,i)) =>
    cond@S(ii,i) =>
      SCpt(i)@pred(S(ii,i)) ~< SCpt(i)@S(ii,i) = orderOk.
(** The proof is automatically done by Squirrel. *)
Proof. auto. Qed.

(** The counter `SCpt(i)` increases (not strictly) between `pred(t)`
and `t`. *)
lemma counterIncrease (t:timestamp, i : index) :
  happens(t) =>
    (t > init && exec@t) =>
      (SCpt(i)@pred(t) ~< SCpt(i)@t = orderOk) ||
       SCpt(i)@t = SCpt(i)@pred(t).
Proof.
  (** After having introduced the hypotheses, we perform a case analysis
  on all possible values that the timestamp `t` can take.
  Most cases are trivial and automatically handled by Squirrel (`=> //`)
  because most actions do not update `SCpt(i)` so we automatically have
  that `SCpt(i)@t = SCpt(i)@pred(t)`. *)
  intro Hap [Ht Hexec].
  case t => //.

  (** Case where t = S(ii,i0):
  This is the interesting case, where `t` is an action that updates the
  mutable cell `SCpt(i0)`.
  We distinguish two cases: `i = i0` and `i <> i0`. *)
  intro [ii i0 _].
  case (i = i0) => _.
      (** The case `i = i0` corresponds to the left disjunct, which is a
      direct consequence of the condition of the action `SCpt(i)`.
      This is done automatically by Squirrel. *)
    + by rewrite if_true //. 
      (** The case `i <> i0` corresponds to the right disjunct. When expanding
      the macro `SCpt(i)@t`, we notice that it is an `if _ then _ else _` term
      with a condition that is always false. This can be simplified using the
      `rewrite` tactic with lemma `if_false` (which is included in the `Basic`
      library. *)
    + right.
      by rewrite if_false.
    (** The two previous tactics can be merged into a single one:
    by rewrite /SCpt if_false. *)
Qed.

(** The counter `SCpt(i)` increases (not strictly) between `t'` and `t`
when `t' < t`. *)
lemma counterIncreaseBis:
  forall (t:timestamp), forall (t':timestamp), forall (i:index),
    happens(t) =>
      exec@t && t' < t =>
        (SCpt(i)@t' ~< SCpt(i)@t = orderOk || SCpt(i)@t = SCpt(i)@t').
(** This proof is done by induction, relying on the previous `counterIncrease`
lemma to prove the induction step. *)
Proof.
  induction.
  intro t IH0 t' i Hap [Hexec Ht'].
  (** We introduce a case disjunction `t'`. Since we already have that
  `t' < t` then the `constraints` tactic allows to close the lemma showing
  that `(t' = pred(t) || t' < pred(t))` is indeed satisfied. *)
  assert (t' = pred(t) || t' < pred(t)) as H0;
    1: constraints.
  case H0.

    (** **Case t' = pred(t).**
    We first rewrite the conclusion using the equality in H0. The `!` mark is
    here to indicate that the rewriting must be done as much as possible and
    at least once.
    Then, it is a direct consequence of the `counterIncrease` lemma. *)
  + rewrite !H0.
    by apply counterIncrease.

    (** **Case t' < pred(t).**
    We first apply the induction hypothesis with `t' < pred(t)` to obtain a
    relation between `SCpt(i)@t'` and `SCpt(i)@pred(t)`.
    We then use the `counterIncrease` lemma, this time to obtain a relation
    between `SCpt(i)@pred(t)` and `SCpt(i)@t`.
    We will then be able to conclude by transitivity.
    *)
  + use IH0 with pred(t),t',i as H1 => //.
      - use counterIncrease with t,i as H3 => //.
        case H1 => //.
        * (* case H1 - 1/2 *)
          case H3 => //.
          by left; apply orderTrans _ (SCpt(i)@pred(t)) _.
        * (* case H1 - 2/2 *)
          by case H3; [1: left | 2 : right].

       (** It remains to show that the premises of the induction hypothesis IH0
       were satisfied, relying on the fact that `exec@t => exec@pred(t)`. *)
     - simpl.
       executable t => // H1.
       by apply H1.
Qed.

(** #### SECURITY PROPERTIES

We now state and prove the 3 following security properties:

* Property 1: absence of replay attacks.
* Property 2: injective correspondence.
* Property 3: monotonicity.

******************************************
*)

(**
#### Property 1: absence of replay attacks
This property states that the server never accepts for the same YubiKey the
same counter twice, _i.e._ if the trace is executable up until `S(ii1,i)`,
then there cannot exist a previous action `S(ii,i)` in the trace such that
`ii <> ii1` and `SCpt(i)@S(ii,i) = SCpt(i)@S(ii1,i)`.

Note that proving this property does not rely on any assumption on cryptographic
primitives: it relies only on reasonings about counter values.
*)

(**
We start by proving an invariant (`noreplayInv`) that will be useful in the
main proof.
This intermediate lemma states that whenever the server accepts for a given
YubiKey (represented by the index `i`), the counter value must have increased
compared to the last time the server accepted for this YubiKey.
*)
lemma noreplayInv (ii, ii1, i:index):
  happens(S(ii1,i),S(ii,i)) =>
  exec@S(ii1,i) && S(ii,i) < S(ii1,i) =>
  SCpt(i)@S(ii,i) ~< SCpt(i)@S(ii1,i) = orderOk.
(** The proof relies on the previous helping lemmas reasoning on counter
values. *)
Proof.
  intro Hap [Hexec Ht].
  assert (S(ii,i) = pred(S(ii1,i)) || S(ii,i) < pred(S(ii1,i))) as H1;
    1: constraints.
  case H1.
    + (* Case S(ii,i) = pred(S(ii1,i)). *)
      by use counterIncreaseStrictly with ii1, i as M0.

    + (* Case S(ii,i) < pred(S(ii1,i)). *)
      use counterIncreaseBis with pred(S(ii1,i)),S(ii,i),i as H2 => //.
      case H2 => //.
      by apply orderTrans _ (SCpt(i)@pred(S(ii1,i))) _.
Qed.

lemma noreplay (ii, ii1, i:index):
  happens(S(ii1,i)) =>
    exec@S(ii1,i) && S(ii,i) <= S(ii1,i) && SCpt(i)@S(ii,i) = SCpt(i)@S(ii1,i) =>
      ii = ii1.
Proof.
  intro Hap [Hexec Ht Meq].
  assert (S(ii,i) = S(ii1,i) || S(ii,i) < S(ii1,i)) as H1;
    1: constraints.
  (** The case where `S(ii,i) = S(ii1,i)` is trivial and automatically
  handled by Squirrel.
  For the case where `S(ii,i) < S(ii1,i)`, we use the invariant to show that
  there is a contradiction with the hypothesis Meq. *)
  case H1 => //.
  use noreplayInv with ii, ii1, i as M1 => //.
  by apply orderStrict in Meq.
Qed.


(** #### Property 2: injective correspondence
This property states that a successful login for the YubiKey `pid(i)`
(_i.e._ the execution of action `S(ii,i)`) must have been preceded by
a button press on this YubiKey for the same counter value (`P(i,j)` with
`cpt(i,j)@Press(i,j) = SCpt(i)@S(ii,i)`), and this counter value is not
involved in another successful login.

Proving this property requires to reason on counter values, but also requires
the use of the INT-CTXT cryptographic assumption.
*)
lemma injective_correspondence (ii,i:index):
  happens(S(ii,i)) =>
  exec@S(ii,i) =>
  exists (j:index),
    Press(i,j) < S(ii,i) && cpt i j@Press(i,j) = SCpt(i)@S(ii,i) && 
    forall (ii1:index), 
      happens(S(ii1,i)) => 
      exec@S(ii1,i) =>
      cpt i j@Press(i,j) = SCpt(i)@S(ii1,i) => 
      ii1 = ii.
(** The high-level idea of this proof is to use the INT-CTXT assumption:
if the message received by the server is a valid ciphertext, then it must
be equal to an encryption that took place before.

Since the action `Press(i,j)` is the only one that outputs an encryption,
we thus have the existence of such an action before in the trace.
Then, the unicity is proved using lemmas on counter values.
*)
Proof.
  intro Hap Hexec.
  executable S(ii,i) => //.
  intro Hexec'. 
  rewrite /exec /cond in Hexec.
  destruct Hexec as [Hexecpred [Mneq Hcpt] Hpid].
  (** We apply the INT-CTXT assumption, which directly gives the existence
  of an action `Press(i,j)` that happens before `S(ii,i)`. *)
  intctxt Mneq => //.
  (* randomness condition *)
  ++ intro [j [Ht M1]].  
    exists j.

  (** The two first conjucts of the conclusion are automatically proved
  by Squirrel (the equality of counter values is a consequence of M1 once
  we have expanded the macros `cpt` and `SCpt`. *)
  simpl. 
  split; 1: auto.
  (** It now remains to show that the counter value `cpt i j@Press(i,j)` is
  not involved in another successful login.
  We first show if this second successful login `S(ii',i)` had happened, then
  we must have `SCpt(i)@S(ii,i) = SCpt(i)@S(ii',i)`. *)
  intro ii' Hap' Hexec1 Eq.
  assert (SCpt(i)@S(ii,i) = SCpt(i)@S(ii',i)) => //.
  (** The proof now relies only on lemmas about counter values to show that
  we cannot have `SCpt(i)@S(ii,i) = SCpt(i)@S(ii',i)` and `S(ii,i) <> S(ii',i)`.
  We therefore a case disjunction (the first case corresponds to what we want
  to prove, and we will show that the 2 other cases are impossible). *)
  assert (S(ii,i) = S(ii',i) || S(ii,i) < S(ii',i) || S(ii,i) > S(ii',i)) => //.
  case H; 1:auto. 

    + (* 1st case: S(ii,i) < S(ii',i) *)
      assert (S(ii,i) = pred(S(ii',i)) || S(ii,i) < pred(S(ii',i))) by auto. 
      case H0.

        - (* S(ii,i) = pred(S(ii',i) < S(ii',i) *)
          use counterIncreaseStrictly with ii',i; 2: auto. 
          * subst  S(ii,i), pred(S(ii',i)) => //.
            by use orderStrict with SCpt(i)@pred(S(ii',i)), SCpt(i)@S(ii',i) => //.
          * rewrite /cond.
            rewrite /exec /cond in Hexec1.
            destruct Hexec1 as [H1 [H2 H22] H3]. 
            clear Eq H H0 Mneq Meq M1 Ht Hexec' Hap Hap' Hexecpred.
            auto.

        - (* S(ii,i) < pred(S(ii',i))  < S(ii',i) *)
          use counterIncreaseStrictly with ii',i; 2,3: auto. 
          use counterIncreaseBis with pred(S(ii',i)), S(ii,i), i; 2,3:auto. 
          case H1.
            * use orderTrans with
                SCpt(i)@S(ii,i), SCpt(i)@pred(S(ii',i)), SCpt(i)@S(ii',i); 
              2,3: auto. 
              by use orderStrict with SCpt(i)@S(ii,i), SCpt(i)@S(ii',i). 
            * subst SCpt(i)@pred(S(ii',i)), SCpt(i)@S(ii,i).
              by use orderStrict with SCpt(i)@S(ii,i), SCpt(i)@S(ii',i). 

    + (* 2nd case: S(ii,i) > S(ii',i) *)
      assert (pred(S(ii,i)) = S(ii',i) || pred(S(ii,i)) > S(ii',i)) by auto. 
      case H0.

        - (* S(ii,i) > pred(S(ii,i)) = S(ii',i) *)
          use counterIncreaseStrictly with ii,i; 2,3:auto. 
          subst S(ii',i), pred(S(ii,i)).
          by use orderStrict with SCpt(i)@pred(S(ii,i)), SCpt(i)@S(ii,i).

        - (* S(ii,i) > pred(S(ii,i)) >  S(ii',i) *)
          use counterIncreaseStrictly with ii,i; 2,3: auto. 
          use counterIncreaseBis with pred(S(ii,i)), S(ii',i), i; 2,3:auto. 
          case H1.
            * use orderTrans
                with SCpt(i)@S(ii',i), SCpt(i)@pred(S(ii,i)), SCpt(i)@S(ii,i); 
              2,3:auto. 
              by use orderStrict with SCpt(i)@S(ii',i), SCpt(i)@S(ii,i). 
            * subst SCpt(i)@pred(S(ii,i)), SCpt(i)@S(ii',i).
              by use orderStrict with SCpt(i)@S(ii',i), SCpt(i)@S(ii,i).
Qed.



(** #### Property 3: monotonicity
This property states that the counter values associated to successful logins are
monotonically increasing in time.

Note that proving this property does not rely on any assumption on cryptographic
primitives: it relies only on reasonings about counter values.
*)
lemma monotonicity (ii, ii1, i:index):
  happens(S(ii1,i),S(ii,i)) =>
    exec@S(ii1,i) && exec@S(ii,i)
      && SCpt(i)@S(ii,i) ~< SCpt(i)@S(ii1,i) = orderOk =>
        S(ii,i) < S(ii1,i).
Proof.
  intro Hap [Hexec H].
  (** We introduce a case disjunction, and we will show that the cases
  `S(ii,i) = S(ii1,i)` and `S(ii,i) > S(ii1,i)` are not possible, relying
  on previous lemmas and axioms on counter values. *)
  assert
    (S(ii,i) = S(ii1,i) || S(ii,i) < S(ii1,i) || S(ii,i) > S(ii1,i)) as Ht;
  1: constraints.
  case Ht.

  + (* case S(ii,i) = S(ii1,i) *)
    by use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii,i).

  + (* case S(ii,i) < S(ii1,i) *)
    assumption.

  + (* case S(ii,i) > S(ii1,i) *)
    use noreplayInv with ii1, ii, i as Meq => //.
    use orderTrans with SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i), SCpt(i)@S(ii,i) => //.
    by use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii,i).
Qed.

