system null.
goal dummy : True.

Proof.
nosimpl(help).
nosimpl(help concise).
help euf.
Qed.

equiv test: diff(zero,zero).
Proof.
nosimpl(help).
nosimpl(help concise).
help fresh.
Qed.
