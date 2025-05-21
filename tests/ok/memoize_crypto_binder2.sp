include Core.

channel c.

type key.
type rand.

op enc : message -> rand -> key -> message.
op dec : message -> key -> message.

game CCA2 = {
  rnd key : key;
  var log = empty_set;

  oracle lr m0 m1 = { 
    rnd r : rand;
    var e = enc (diff(m0,m1)) r key;
    log := add e log;
    return e; 
  }

  oracle dec c = {
    return if not (mem c log) then dec c key else witness;
  }
}.

op format ['a] : 'a -> message.

(* ------------------------------------------------------ *)
name k : key.
name r : rand.
 
action A : 0.
action B : 1.

set verboseCrypto=true.
system Q = 
  A: in(c,x); out(c, enc (diff(x,empty)) r k) |
  !_i 
    B: in(c,y);
       out(c, format (if A < B i && y = enc (diff(input@A,empty)) r k
                      then witness
                      else dec y k)).

global lemma _ @system:Q (t:_[adv]) :
  [happens t] -> equiv(frame@t).
Proof.
  intro Hap.

  (* Time-sensitive memory invariant should be needed to show that the
     synthesized simulator is correct. *)
  checkfail by crypto CCA2 exn GoalNotClosed.

  crypto ~time_sensitive CCA2. 
  + auto. + auto. + auto.
  cycle 1.
  + intro i If_failed i0 [Hap0 Hin_log]. 
    auto.
  + intro i If_failed [Hap0 Hin_log]. 
    auto.
  + intro i If_failed [Hap0 Hin_log].
    auto.
Qed.

global lemma _ @system:Q (t:_[adv]) :
  [happens t] -> [happens A] -> 
  equiv(frame@t, enc (diff(input@A, empty)) r k).
Proof.
  intro Hap HapA.

  checkfail by crypto CCA2 exn GoalNotClosed.
  crypto ~time_sensitive CCA2 => //.
Qed.
