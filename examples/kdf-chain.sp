(*
 * SIGNAL'S SYMMETRIC RATCHET, FRAME-RELATIVE, FOR EVERY POSITION OF A RUN.
 *
 * States the chain against the adversary's whole view of a protocol run -- the
 * statement `stateful/lfmtp21.sp`'s `strong_secrecy` makes, though over a
 * bi-process where it uses a single system, for the reason in the header below
 * -- for a chain keyed in the HASH KEY position, which is Signal's.
 *
 *     equiv(frame@tau, diff(ck@tau, m))
 *
 * over a bi-process whose left projection emits the real message key at each
 * step and whose right emits an independent ideal one:
 *
 *     system S = (!_i A: lock l;
 *                   out(c, diff(hk(lbl_m, ck), nm i));
 *                   ck := hk(lbl_n, ck);
 *                 unlock l).
 *
 * So: at any point of any run, everything the adversary has seen together with
 * the chain key it retains is indistinguishable from independent randomness.
 *
 * WHY IT IS SHAPED THIS WAY. The `diff` has to sit in the PROCESS, not in the
 * lemma. Stating `equiv(frame@tau, diff(ck@tau, m))` over a single system leaves
 * the REAL message keys on both sides of the equivalence, which is not the
 * statement wanted; a bi-process idealises them. The single-system control
 * (control 4) is that collapse, and it dies naming the obstruction:
 * `Term hk (lbl_m, ck@pred (A(i))) is not a name.`
 *
 * WHY THE MUTEX. It makes one ratchet step atomic, which is what puts the
 * emission and the advance in a SINGLE action. With the lock, Squirrel reports
 * `System S registered with actions (init,A)` and `ck@A(i)` is the advanced key.
 * Without it the same process compiles to `(init,A,A1)` -- the update becomes
 * its own action, `ck@A(i)` is the key BEFORE the step, and Squirrel reports
 * `Found 3 conflicts` between the read and the write across sessions. The lock
 * is the model of the fact that the party advancing the chain is the party that
 * just used it.
 *
 * THE PROOF. `trans` moves the derived key to a name, one leg is the induction
 * hypothesis, and only then does `prf` apply -- twice, the first emitting
 *
 *     exec@pred (A(i)) && true => lbl_m <> lbl_n
 *
 * the domain-separation obligation, discharged by `labels_distinct`. The
 * `&& true` is `cond@A(i)`, which is `true` because the action carries no
 * condition. A message-position chain never meets this. `stateful/lfmtp21.sp:15` is the
 * upstream one -- `(A: !_i lock l; s:=H(s,k); out(o,G(s,k')); unlock l)` -- and
 * its key `k` is a name (`:3`), so it calls `prf` directly (`:194`, `:204`,
 * `:220`, `:230`), with no `trans` and no relation between derivations. That
 * line is also the precedent for the lock above: upstream models a stateful
 * chain the same way.
 *
 * WHAT THE TWO CRYPTO STEPS ACTUALLY DISCHARGE, since `prf`'s output is easy
 * to misread. Each `prf` reports occurrences of the key on BOTH projections,
 * but only the one it rewrites can carry an obligation:
 *
 *   - the first `prf` finds, on the LEFT, `lbl_n` hashed by `m` colliding with
 *     `lbl_m` hashed by `m`, and emits the domain-separation goal above;
 *   - both applications also report `m (collision with m)` on the RIGHT and
 *     emit nothing for it. That is correct rather than a gap: `prf` rewrites
 *     the left projection, and the right is a different world in which no PRF
 *     game is being played. `m` never occurs on the LEFT except as the key --
 *     it appears in no output, so it is absent from `frame@pred (A(i))`. Expose
 *     it there instead and `prf` does emit the obligation, which is the check
 *     that this reading is not wishful.
 *
 * The two freshness conditions are:
 *
 *     fresh (the message key)   forall (i0:index), A(i0) < A(i) => i <> i0
 *     fresh (the chain key)     true
 *
 * The first says the ideal key emitted at this step is not one already
 * idealised, and nothing has to assume it: `A(i0) < A(i)` makes `i0 = i`
 * impossible because `<` on timestamps is irreflexive. Stated over an abstract
 * position order, that step needs an axiom. The second is trivial, because the
 * ideal chain key appears nowhere in the frame.
 *
 * ONE TIME, NOT TWO. `stateful/lfmtp21.sp:179-181` quantifies its chain-key
 * time separately from its frame time; this does not, because for a chain
 * separated by LABELS under one key that form is false. Take the earlier time:
 * the process emits `hk(lbl_m, ck)`, so the frame already holds a hash of that
 * chain key, and an adversary given the key recomputes it and finds a match --
 * where the ideal side holds independent names and nothing matches.
 *
 * ONE AXIOM. `labels_distinct` is the only assumption. Stating the same chain
 * over an abstract position order instead would need a predecessor, a zero and
 * an order axiomatised on top of it; indexing on timestamps costs none of that,
 * because Squirrel's own `pred` and well-founded `<` already supply it.
 *
 * CONTROLS, each of which must fail and does:
 *   1. `labels_distinct` flipped to `lbl_n = lbl_m`   -- domain separation
 *   2. the ideal message keys all made the same name  -- their independence
 *   3. the process emitting `ck` instead of `hk(lbl_m, ck)` -- the chain key
 *      itself is not public
 *   4. the bi-process collapsed to a single system    -- the modelling decision
 *   5. the ideal chain key drawn from the emitted family -- its independence
 *      from them
 *
 * 2 and 5 falsify: each dies on the mathematics, at the condition the mutation
 * withdrew. 1, 3 and 4 fail structurally -- 1 because any mutation of
 * `labels_distinct` breaks the `apply` that discharges the obligation before
 * the mathematics is reached, 3 and 4 because changing the process changes the
 * goal's shape. They still pin the obligation, the modelling of the emitted
 * value, and the bi-process.
 *
 * Verifies on `1ce3981` and on `master` 69d926d.
 *)

include Core.

channel c.
mutex l:0.

hash hk.
abstract lbl_m : message.
abstract lbl_n : message.
axiom [any] labels_distinct : lbl_n <> lbl_m.

name ck0 : message.
name nm  : index -> message.
name m   : message.

mutable ck : message = ck0.

(* The ratchet as a BI-PROCESS: the left projection emits the real message key,
   the right an independent ideal one. The chain advances identically on both
   sides. Putting the `diff` in the PROCESS rather than in the lemma is the
   structural point -- see the header. *)
system S = (!_i A: lock l;
              out(c, diff(hk(lbl_m, ck), nm i));
              ck := hk(lbl_n, ck);
            unlock l).

global lemma [set:S/left,S/right; equiv:S/left,S/right]
  ratchet (tau:timestamp[const]) :
    [happens(tau)] -> equiv(frame@tau, diff(ck@tau, m)).
Proof.
  induction tau => Htau.

  (* init: the frame collapses, leaving the root chain key against a name *)
  - expand frame@init. by fresh 0.

  (* A(i): three parts -- the accumulated view, the message key, and the next
     chain key -- with the next chain key idealising to `m` itself *)
  - expand frame, exec, cond.
    fa 0; fa 1.
    (* the two legs: the induction hypothesis, and the crypto step on a NAME key *)
    trans 1: (if (exec@pred (A(i)) && true) then hk (lbl_m, m)), 2: hk(lbl_n, m).
    + by apply IH.
    + prf 1; 1: (by intro _; rewrite neq_sym; apply labels_distinct). fa 1; fresh 1; 1: auto. prf 1; fresh 1; 1: auto. by auto.
Qed.
