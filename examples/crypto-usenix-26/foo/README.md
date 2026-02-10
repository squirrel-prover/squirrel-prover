**Note:** in this sub-directory, includes are marked with `[admit]`,
to allow to separately checked each file without re-checking the same
proof multiple times through includes. If all files are individually
verified (which `make test` does), then this has no consequence. A
more clever handling of includes by Squirrel could allow to avoid
this kind of tricks.

## Formal proof of vote privacy for FOO

The main security lemma can be found in `main.sp`.

The main (bi)system is `Privacy_real`, defined in `processes.sp` together
with its variant `Privacy_CCA` where only zeroes are encrypted.

The proof is in three main steps:

(1) Prove that `Privacy_real/left` is indistinguishable from
    `Privacy_CCA/left` and similarly on the right.
    This is done using two reductions to CCA2 for each of the mix-nets'
    keys.

(2) We do a case analysis on whether the two honest votes fully go through.
    In case they do, we show that privacy is a consequence of the
    blinding property.

(3) Otherwise, we conclude by commitment hiding.

## Organization

### Model: definitions, assumptions, utilities and glue

- Libs.sp
- Games.sp
- processes.sp
- macros.sp
- main.sp

### CCA2 reductions

We show that `Privacy_real/left` is indistinguishable from `Privacy_CCA/left`,
and similarly on the right, by reduction to the CCA2 game.

- ccapk1.sp
- ccapk2.sp
- cca.sp

### Proof on Privacy_CCA

The proof branches depending on whether the two votes are cast.
In each case we work by reducing the goal to a core bi-deduction goal,
opening the shuffles differently in the two branches of the proof.
The final argument is by the blinding property of signature when two votes
are cast, and the commitment hiding property otherwise, but auxiliary
cryptographic arguments are used in both cases.

The following files deal with the reduction (using bi-deduction) of the
equivalences to simpler terms, notably opening shuffles by applying the
appropriate permutations:

- shuffle.sp
- deduction.sp
- reduction.sp

The cryptographic arguments that are instrumental in the deduction, or
used to complete the privacy proof, are in the following files:

- blinding.sp
- commitKeySecrecy.sp
- commitSecrecy.sp
- distinctCommits.sp
- distinctEncryptions.sp
- voteHiding.sp
