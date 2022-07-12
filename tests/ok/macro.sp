

channel c

abstract a : message
abstract b : message.

process P = 
  in(c,x);
  let y = a in
  P: out(c,y).

process Q = 
  in(c,x);
  let z = b in
  Q: out(c,z).

system (P | Q).

goal _: happens(Q) => z@Q=a.
Proof. 
 intro Hap. 
 expand z@Q.
 checkfail congruence exn CongrFail.
Abort.
