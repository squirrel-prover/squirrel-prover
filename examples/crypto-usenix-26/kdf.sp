include Core.

channel c.

type key.

op h : message * key -> message.

name k : key.

game PRF = {
  rnd key : key;
  var lhash = empty_set; (* Log for ohash queries.     *)
  var lchal = empty_set; (* Log for challenge queries. *)

  oracle ohash x = {
    lhash := add x lhash;
    return if mem x lchal then zero else h(x,key)
  }

  oracle challenge x = {
    rnd r : message;
    var old_lchal = lchal;
    lchal := add x lchal;
    return if mem x old_lchal || mem x lhash then zero else diff(h(x,key), r)
  }
}.

op format : string -> message.

name nF : message.

system 
  (A: out(c, diff(h(format "A", k), nF)) |
  !_i (B: in(c,x); 
          out(c, if x = format "A" then
                   diff(h(format "A", k), nF)
                 else h(x,k)))).

set verboseCrypto=true.


global lemma _ (t:_[adv]) : equiv(frame@t).
Proof.
  crypto 
    ~no_subgoal_on_failure
    ~no_memoization
    PRF;
  try auto.
 (* This fails for at least two reasons:
    - The time-insensitive invariant for `lchal`

        lchal → [{ format "A" | A <= t },
                 { format "A" | ∀ i0 : input@B(i0) = format "A" && B(i0) <= t } ]

      creates unprovable subgoals. E.g. in action `A`, we must prove
      that `format "A" ≠ format "A"` (due to the first item in
      `lchal`) because the analysis does not know that `A` was not yet
      executed (and thus that `(format "A" | A ≤ t)` is not yet in `lchal`).

    - The absence of memoization across actions yield the local name constraints:

       { nF , L | ∀ i0 : input@B(i0) = format "A" && B(i0) <= t } 
       { nF , L | A <= t }

      which lead to unprovable the subgoals. E.g. we must show that
      that either `A` is never scheduled, or no action `B i` was
      scheduled (the adversary may always ensure that `input@B(i0) =
      format "A"`, making this requirement easy to fullfill). *)


  (* Sanity check: `smt` does not manage to close the generated goals
     (when we turn-on both memoization and time-sensitive invariants
     below, `smt` will manage to close all subgoals). *)
  + checkfail (smt ~steps:40000) exn Failure. admit.
  + checkfail (smt ~steps:40000) exn Failure. admit.
  + checkfail (smt ~steps:40000) exn Failure. admit.
  + checkfail (smt ~steps:40000) exn Failure. admit.
  + checkfail (smt ~steps:40000) exn Failure. admit.
  + checkfail (smt ~steps:40000) exn Failure. admit.
Qed.


global lemma _ (t:_[adv]) : equiv(frame@t).
Proof.
  crypto 
    ~no_subgoal_on_failure
    ~no_memoization
    ~time_sensitive             (* turn-on the time-sensitive invariant inference *)
    PRF;
  try auto.
 (* - This solves the first issue above, as we know get the information
      that at time `τ0`, the log `lchal` contains:
      
        lchal → [{ format "A" | ∀ τ0 : A < τ0 && τ0 <= t },
                 { format "A" |
                     ∀ i0,τ0 :
                       input@B(i0) = format "A" && B(i0) < τ0 && τ0 <= t } ]

    - The second issue due to the absence of memoization remains, and
      we get the same name constraints as above (which are still
      unprovable). *)

  (* Sanity check: `smt` does not manage to close the generated goals
     (when we turn-on both memoization and time-sensitive invariants
     below, `smt` will manage to close all subgoals). *)
  + checkfail (smt ~steps:40000) exn Failure. admit.
  + checkfail (smt ~steps:40000) exn Failure. admit.
  + checkfail (smt ~steps:40000) exn Failure. admit.
  + checkfail (smt ~steps:40000) exn Failure. admit.
  + checkfail (smt ~steps:40000) exn Failure. admit.
Qed.

global lemma _ (t:_[adv]) : equiv(frame@t).
Proof.
  crypto ~no_subgoal_on_failure ~time_sensitive PRF => //.

  (* `smt` concludes in all cases. *)
  + smt ~steps:40000.
  + smt ~steps:40000.
  + smt ~steps:40000.
  + smt ~steps:40000.
Qed.
