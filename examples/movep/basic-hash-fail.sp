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

This file shows an incorrect attempt at proving unlinkability for Basic
Hash. Unlinkability fails for the proposed system, for an irrelevant
reason.

[A] Mayla Brusò, Kostas Chatzikokolakis, and Jerry den Hartog. Formal
Verification of Privacy for RFID Systems. pages 75–88, July 2010.

*)

hash h

abstract ok : message
abstract ko : message.

(* In the single session system `tag(i,k)` will use `key'(i,k)`
   instead of `key(i)`. *)
name key  : index -> message.
name key' : index * index -> message.

channel cT
channel cR.

(** Use `diff` operator to specify multiple session (left)
    and single session (right) roles simultaneously. *)
process tag(i:index,k:index) =
  new nT;
  out(cT, <nT, h(nT,diff(key(i),key'(i,k)))>).

(** Session `j` of reader.
    For single-session version we need to find `k` in addition
    to `i`. *)
process reader(j:index) =
  in(cT,x);
  try find i,k such that snd(x) = h(fst(x),diff(key(i),key'(i,k))) in
    out(cR,ok)
  else
    out(cR,ko).

system [BasicHash] ((!_j R: reader(j)) | (!_i !_k T: tag(i,k))).

(** Show the set of actions obtained from above process. *)
print system [BasicHash].

(** Prove `wa_R` as in `basic-hash-wa.sp` slightly modified to also
    hold for single-session system.
    The statement (or rather, its projections) is proved for both
    the left and right projections of the `BasicHash` system. *)
goal [BasicHash] wa_R :
  forall (tau:timestamp),
    happens(tau) =>
    ((exists (i,k:index),
       snd(input@tau) = h(fst(input@tau),diff(key(i),key'(i,k))))
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
  intro tau Hap. split => [i k Meq].
  + project. (* Here we need to separate the proof for each projection. *)
    ++ euf Meq => *; by exists i,k0.
    ++ euf Meq => *; by exists i,k.
  (** For the second implication (<=), the conclusion of the goal can directly
       be obtained from the hypotheses.*)
  + by exists i,k.
Qed.

(** There is no hope to prove unlinkability, i.e. the observational equivalence
    of the multiple- and single-session systems.
    Why? *)
