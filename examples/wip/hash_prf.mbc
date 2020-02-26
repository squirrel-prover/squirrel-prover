hash h
channel c

name n : message
name k : message
abstract ok : message

system !_i (out(c,diff(h(ok,k),n)) | out(c,diff(h(ok,k),n))).

equiv [left] [right] test.
Proof.
case t.
expand frame@A1(i).
expand output@A1(i).

(* PRF over h(ok,k), but which appears at two places... *)

(* need to enrich the induction hypothesis to frame@pred(A1)[forall m. h(m,k) ->
if m=ok then n else h(m,k) ], and always expand macros in proof according to this pattern.

Enriching the hypothesis set may try to replay some previous proofs ?

Note that for DDH, one can take a similar appraoch: ddh g^a g^b c :=
enrich the induction hypothesis to frame@pred(A1)[forall x. x^b ->
if x=g^a then g^c else x^b, x^a ->
if x=g^b then g^c else x^a, ], and always expand macros in proof according to this pattern.

*)
