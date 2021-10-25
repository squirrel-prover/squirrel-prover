set autoIntro = false.

hash H.
name k : message.

channel o.
channel c.


system (
   (O: !_i in(o,x); out(o,H(x,k))) 
).


global goal [default/left,default/left]
  strong_secrecy (tau:timestamp) : forall (tau':timestamp),
    [happens(tau)] -> [happens(tau')] -> equiv(frame@tau,
 seq(i:index -> if O(i) <= tau then output@O(i))).  

Proof.
  induction tau => tau' Htau Htau'.

  (* Init *)
admit.

  (* Oracle *)
expand frame@O(i).
fa 0.
fa 1. fa 2. expand exec. fa 1.  expand cond. 
expand output@O(i).


prf 1. 

Qed.
