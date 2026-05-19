This repository contains the case studies for the paper

    David Baelde, Antoine Dallon, Stéphanie Delaune, Charlie Jacomme, Adrien Koutsos:
    Robust Logical Foundations for Mechanizing Post-Quantum Cryptography in Squirrel
    CCS 2026

## Organization

The case studies are organized follow:
- the `bikem/` subfolder contains the proofs of IND-CCA or IND-CPA
  security for several hybrid KEM combiners.
- the `protocols/` subfolder contains the analysis of two hybrid KEM
  key-exchanges (C-SigMA [1] and BCGNP [2]), and a post-quantum variant of the
  Basic Hash protocol.

## Bibliography

[1] Colin Boyd, Yvonne Cliff, Juan Manuel González Nieto, and Kenneth G. Paterson.
    One-round key exchange in the standard model. 
    Int. J. Appl. Cryptogr. 1, 3 (2009), 181–199.
    doi:10.1504/IJACT.2009.023466
    
[2] Nina Bindel, Jacqueline Brendel, Marc Fischlin, Brian Goncalves, 
    and Douglas Stebila.
    Hybrid Key Encapsulation Mechanisms and Authenticated Key Exchange. 
    In Post-Quantum Cryptography - 10th International Conference, PQCrypto 2019.
    doi:10.1007/978-3-030-25510-7_12
