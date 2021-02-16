set autoIntro=false.

(* Simple *)
name n1:message
name n2:message
channel c
system in(c,x);out(c,n1).
goal _ (tau:timestamp): output@tau <> n2.

goal _ (tau1:timestamp, tau2:timestamp):
output@tau1 = output@tau2.

goal _ (tau1:timestamp, tau2:timestamp):
tau1 <> tau2 =>
output@tau1 = output@tau2.

goal _ (tau1:timestamp, tau2:timestamp):
(tau1 <= tau2 &&
output@tau1 = output@tau2)
=>
exists (tau3:timestamp, i:index, i2:index),
(tau1 <= tau3 && tau3 <= tau2) =>
output@tau1 = output@tau2.
