name a : message
name b : message
channel c
system !_i in(c,x);out(c,x).

global goal _ (i:index[const]) : 
  equiv(diff(input@pred(A(i)),a),diff(input@pred(A(i)),b)) ->
  equiv(diff(input@pred(A(i)),a)).
Proof.
  intro H.
  assumption.
Qed.


global goal _ (i:index[const]) :
  equiv(diff(input@pred(A(i)),a),diff(input@pred(A(i)),b)) ->
  equiv(diff(input@pred(A(i)),a)).
Proof.
  intro H.
  apply H.
Qed.
