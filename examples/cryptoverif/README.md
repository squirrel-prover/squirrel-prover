# Experiments with CryptoVerif

## Basic Hash protocol modelling and security
The CryptoVerif authentication and unlinkability proofs for the Basic
Hash protocol are in:
- `basic-hash-auth.pcv`
- `basic-hash-unkink.pcv`


## Alternative modelling and failed attempts

### others/basic-hash-auth-*.pvc

Assuming PRF, authentication is shown for the multiple session scenario,
where each new reader performs a probabilistic choice of the key.
The type of hashed messages must be large for CryptoVerif to conclude.

In basic-hash-auth-keys we use keys rather than hashed messages in events,
and CryptoVerif fails to conclude.

The PRF assumption is stronger than necessary, EUF should suffice.
The variant basic-hash-auth-mac uses a SUF_CMA deterministic mac instead
of the PRF hash, and CryptoVerif concludes. In that case there is no need for 
a large type of MACs, and events can be based on keys rather than MACs.

### others/basic-hash-equiv

Failed attempt to prove unlinkability expressed directly, with a probabilistic 
choice of the key for each new reader.

CryptoVerif attempts to transform both multiple and single-session games,
but each sequence of transformation preserves the general structure of each
process wrt. replications: there is no hope to reach a common game.
In fact the available actions in the two games are not comparable.

The probabilistic choice does not seem to be a problem in itself, since the 
probability that a honest interaction between a tag and a reader is successful
is 1/NK in both games.

### others/basic-hash-diff

Failed attempt to prove unlinkability expressed as an equivalence between
two processes that could be superposed into a bi-process. In that case the
probabilistic choice seems to be a problem (since there are more keys
with the single session scenario, the probability of success is lower)
so we lookup the key against the received hash.

Using find [unique] does not seem to help. Note that the prf equivalence
is not used in the proof attempt.

### others/basic-hash-v2 and -v2-hashoracle

Experiment with a random-oracle assumption: success without the oracle which 
is in principle necessary; could not prove with the oracle -- in that case the 
equivalence rom(hash) even fails to be used.

Note that the nonce that is hashed by the tag is also sent in clear 
(together with the hash) so oracle hashes may coincide with earlier honest 
hashes.

Note that the scenario in this file is for a single tag identity.
