name k : index -> message

abstract ok : message
channel c

system 
 !_i (in(c,x);
      try find j such that x=k(j) in
      out(c,ok) else out(c,x)).

goal not_else (i:index,j:index):
 happens(A1(i)) => cond@A1(i) => output@A1(i) <> k(j).
Proof.
  intro Hap C Heq.
  expand cond@A1(i).
  by use C with j.
Qed.

abstract mess : index -> message

system [test] !_i (
in(c,x);
out(c, diff(try find j,j2 such that j=i && j=j2 in <mess(i),mess(j2)>, 
            try find l,l2 such that l=i && l2=i in <mess(i), mess(l2)>))).

equiv [test] test.
Proof.
  induction t.
  auto.
  expandall.
  fa 0; fa 1; fa 1.
  assert ->:
    try find j,j2 such that (j = i && diff(j,j2) = diff(j2, i)) in 
     <mess(i),mess(j2)>
    =
    try find j,j2 such that (j = i && j = j2) in <mess(i),mess(j2)>.
  by project; fa.
  
  assert ->:
    try find j,j2 such that (j = i && j = j2) in <mess(i),mess(j2)> 
    = 
    <mess(i),mess(i)>. {
    case  try find j,j2 such that (j = i && j = j2) in <mess(i),mess(j2)>.
    + auto.
  
    + intro [H0 _].
      by use H0 with i,i. 
  }.

  auto.
Qed.

(*------------------------------------------------------------------*)
goal _ : zero = try find t,t' : timestamp such that t <= t' in zero else zero.
Proof. 
  by case try find t,t' : timestamp such that _ in _.
Qed.
