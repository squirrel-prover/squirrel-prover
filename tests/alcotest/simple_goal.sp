

(* test *)
name n1:message
name n2:message
(* other test *)
channel c
system out(c,n1).
goal _ (tau:timestamp) : (n1 <> n2) && (n2 = n2).
