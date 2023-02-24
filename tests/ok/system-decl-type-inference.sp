channel c.

process A (res, res' : _) = out(c,<res,res'>).
process B (res : _) (res' : _) = out(c,<res,res'>).
process C res res' = out(c,<res,res'>).

system [A] (A (empty, empty)).
system [B] (B (empty, empty)).
system [C] (C (empty, empty)).

print system [A].
print system [B].
print system [C].
