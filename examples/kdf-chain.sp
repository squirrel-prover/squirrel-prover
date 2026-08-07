(*****************************************************************************

  A SELF-KEYING KDF CHAIN (the Double Ratchet's symmetric ratchet).

  Two chain positions are shown indistinguishable from independent randomness
  to an attacker holding the RETAINED final chain key and BOTH consumed message
  keys -- forward secrecy for the symmetric ratchet of Signal-style protocols:

      ck_{i+1} = hk(lbl_n, ck_i)      advance the chain
      mk_i     = hk(lbl_m, ck_i)      consume a message key

  This shape is not covered by the other examples: here a hash's OUTPUT becomes
  the next hash's KEY. `stateful/toy-state-equiv.sp`, `stateful/slk06.sp` and
  `stateful/yplrk05.sp` all chain in the MESSAGE position with a fixed key, so
  `prf` applies to them directly.

  WHY IT NEEDS THE pq-ccs-2026 TECHNIQUE
  --------------------------------------
  `prf` requires a hash whose key is a NAME, and every chain key past the root
  is derived. Two ingredients from `pq-ccs-2026/bikem/`, from which this
  example is derived, make it go through:

  1. A SEQUENCE OF SYSTEMS (`real`, `middle`, `ideal`), each idealising one
     more position to a fresh NAME in the system definition. Adjacent pairs are
     proved separately and composed with `trans`. Attempting the hybrid inside
     one system instead leaves `A <= t => false`: the idealised value would
     have to be a PRF challenge output and a PRF key simultaneously.

  2. AN ABSTRACT WRAPPER on the outer position (`adv2` / `msg2`, tied to the
     hash by axioms). Without it `prf` refuses to fire on `hk(lbl_n, ck0)`,
     because its occurrence analysis sees `hk(lbl_m, hk(lbl_n, ck0))` -- a hash
     keyed by the very value being idealised. This is the role `dualprf` plays
     in `biKEM_from_KEM_nested_dualPRF1_cpa.sp`; the proof tail here follows
     that file's `StrongSecrecyPart2` closely.

  A NOTE FOR ANYONE ADAPTING THIS: the `fa` peel depth differs per goal --
  three for hop1, two for hop2. Reusing one figure for the other shifts every
  later index, and the resulting failures look cryptographic when they are
  purely arithmetic.

******************************************************************************)

include Core.
close Classic.
open Quantum.
set postQuantumEquivs = true.

hash hk.
abstract lbl_n : message.
abstract lbl_m : message.
axiom [any] labels_distinct : lbl_n <> lbl_m.

(* The SECOND-position derivations, wrapped in ABSTRACT symbols so that
   occurrence analysis does not see them as hashes keyed on the value we are
   idealising. Exactly the role dualprf plays in the CCS-2026 nested combiner:
   stay abstract while the inner PRF is applied, rewrite to hash form after. *)
abstract adv2 : message -> message.
abstract msg2 : message -> message.
axiom [any] adv2_def (x:message) : adv2 x = hk(lbl_n, x).
axiom [any] msg2_def (x:message) : msg2 x = hk(lbl_m, x).

name ck0 : message.
name k1  : message.
name m0  : message.
name n2  : message.
name m1  : message.
name m0b : message.

channel c.

process P_real  = out(c, < adv2(hk(lbl_n, ck0)),
                         < hk(lbl_m, ck0), msg2(hk(lbl_n, ck0)) > >).
system [postquantum] real = (Out: P_real).

process P_mid   = out(c, < adv2(k1), < m0, msg2(k1) > >).
system [postquantum] middle = (Out: P_mid).

process P_ideal = out(c, < n2, < m0b, m1 > >).
system [postquantum] ideal = (Out: P_ideal).

(* ------------------------------------------------------------------------ *)
(* HOP 1 -- idealising a DERIVED key. The hard one.                          *)
(* ------------------------------------------------------------------------ *)
global theorem [set: real; equiv: real/left, middle/left]
  hop1 (tau:timestamp[const,glob]) :
 [happens(tau)] -> equiv(frame@tau).
Proof.
  intro Hap.
  induction tau.
  + rewrite /frame. auto.
  + rewrite /frame /transcript /output.
    fa (_,_,_), !<_,_>.
    (* `prf` fires on the INNER hash: its key ck0 is a name, and the outer
       level is hidden inside the abstract adv2/msg2. Each application emits a
       domain-separation obligation -- that is what lbl_n <> lbl_m is for. *)
    prf 5, hk(lbl_n, ck0).
    - by intro _ _; apply labels_distinct.
    - prf 5, hk(lbl_m, ck0).
      * auto.
      (* The payload is now two independent fresh-name diffs; the rest is the
         frame recursion, closed on the induction hypothesis. *)
      * fa 5. fa 5. fa 5. fa 6. fresh 6; 1:auto. fresh 5; 1:auto.
        rewrite /input /state. fa 1. fa(qatt _). {auto. } apply IH.
Qed.

(* ------------------------------------------------------------------------ *)
(* HOP 2 -- the outer position, now keyed on the fresh name k1.              *)
(* ------------------------------------------------------------------------ *)
global theorem [set: real; equiv: middle/left, ideal/left]
  hop2 (tau:timestamp[const,glob]) :
 [happens(tau)] -> equiv(frame@tau).
Proof.
  intro Hap. induction tau.
  + rewrite /frame. auto.
  + rewrite /frame /transcript /output.
    rewrite adv2_def msg2_def.
    fa (_,_,_), !<_,_>.
    prf 5, hk(lbl_n, k1).
    - by intro _ _; apply labels_distinct.
    - prf 5, hk(lbl_m, k1).
      * auto.
      (* Two `fa 5` here, not three as in hop1: re-derive the peel depth from
         the goal rather than copying it across. *)
      * fa 5. fa 5. fa 6.
        fresh 7; 1:auto. fresh 6; 1:auto. fresh 5; 1:auto.
        rewrite /input /state. fa 1. fa(qatt _). {auto. } apply IH.
Qed.

(* ------------------------------------------------------------------------ *)
(* THE CHAIN. Composed by `trans` through the intermediate system. Both hops *)
(* are stated in the same `set:` context so the transitivity goes through.   *)
(* ------------------------------------------------------------------------ *)
global theorem [set: real; equiv: real/left, ideal/left]
  chain2_fs (tau:timestamp[const]) :
 [happens(tau)] -> equiv(frame@tau).
Proof.
  intro Hap.
  trans [middle/left, middle/left].
  + by apply hop1.
  + auto.
  + by apply hop2.
Qed.
