(**

# BASIC HASH

The Basic Hash protocol as described in [A] is an RFID protocol involving:

* a tag associated to a secret key;
* generic readers having access to a database containing all these keys.

The protocol is as follows:

```
T --> R : <nT, h(nT,key)>
R --> T : ok
```

In this file, we prove an authentication property for the reader.

[A] Mayla Brusò, Kostas Chatzikokolakis, and Jerry den Hartog. Formal
Verification of Privacy for RFID Systems. pages 75–88, July 2010.

*)

(** Include basic standard library. *)
include Basic.

(** We start by declaring the function symbol `h` for the hash function,
    as well as two public constants `ok` and `ko` (used by the reader). *)

hash h

abstract ok : message
abstract ko : message.

(** Name for modelling the keys of tags. *)

name key  : index -> message.

(** Finally, we declare the channels used by the protocol. *)

channel cT
channel cR.

(** Session `k` of tag `i`. *)
process tag(i:index,k:index) =
  new nT;
  out(cT, <nT, h(nT,key(i))>).

(** Session `j` of reader. *)
process reader(j:index) =
  in(cT,x);
  try find i such that snd(x) = h(fst(x),key(i)) in
    out(cR,ok)
  else
    out(cR,ko).

system [BasicHash] ((!_j R: reader(j)) | (!_i !_k T: tag(i,k))).

(** Show the set of actions obtained from above process. *)
print system [BasicHash].

(** Whenever a reader accepts a message (_i.e._ the condition of the action
    `R(j)` evaluates to `true`), there exists an action `T(i,k)` that has been
    executed before the reader, and such that the input of the reader
    corresponds to the output of this tag (and conversely).

    The same holds for `R1` (the else branch of the reader) but with a negation.
    We will prove once and for all a property that is generalized for any
    `tau`, which will be useful later for `tau = R(j)` and `tau = R1(j)`. *)
goal [BasicHash] wa_R :
  forall (tau:timestamp),
    happens(tau) =>
    ((exists (i:index),
       snd(input@tau) = h(fst(input@tau),key(i)))
     <=>
     (exists (i,k:index), T(i,k) < tau &&
       fst(output@T(i,k)) = fst(input@tau) &&
       snd(output@T(i,k)) = snd(input@tau))).
(** The high-level idea of the proof is to use the EUF cryptographic axiom:
    only the tag `T(i,k)` can forge `h(nT(i,k),key(i))` because the secret key
    is not known by the attacker.
    Therefore, any message accepted by the reader must come from a tag that has
    played before.
    The converse implication is trivial because any honest tag output is
    accepted by the reader. *)
Proof.
  intro tau Hap. split.
  + intro [i Meq].
    (** Applying the `euf` tactic on the `Meq` hypothesis generates a new
        hypothesis stating that `fst(input@R(j))` must be equal to some message
        that has already been hashed before.
        The only possibility is that this hash comes from the output of a tag
        that has played before (thus the new hypothesis on timestamps).*)
    euf Meq => *. exists i,k. auto.
  (** For the second implication (<=), the conclusion of the goal can directly
       be obtained from the hypotheses.*)
  + intro [i k Meq]. exists i. auto.
Qed.
