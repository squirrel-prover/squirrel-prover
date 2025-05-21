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
name r : index -> rand.
 
action A : 1.
action B : 0.

system Q = 
  !_i ( A: in(c,x); out(c, enc (diff(x,format i)) (r i) k) ) |
  B: in(c,y);
     out(c, format (if exists i0, 
                        A i0 < B && y = enc (diff(input@A i0,format i0)) (r i0) k
                    then witness
                    else dec y k)).

global lemma _ @system:Q (t:_[adv]) :
  [happens t] -> equiv(frame@t).
Proof.
  intro Hap.

  crypto ~time_sensitive CCA2 => //.
  rewrite !not_exists_1 /=.
  intro [H0 H1] i [G0 G1 G2 G3].
  clear H0 H1 G3. (* duplicated hypotheses *)
  have ? := G0 i.
  auto. 
Qed.
