This repository contains the novel case-studies for the paper

    Caroline Fontaine, Adrien Koutsos, Guillaume Scerri, Théo Vignon:
    Interactive Proofs in Higher-Order Logic with
    Errors and Application to Concrete Cryptography. 
    CSF 2026

## Organization

The case studies are organized follow:
- the examples of sections 2 and 3 of the paper are in ``companion.sp``.
- `birthday_paradox.sp` for the birthday paradox in the concrete setting.
- `birthday_paradox_exact.sp` for an exact variant of the birthday
  paradox assuming a perfect (collision-free) hash function.
- `merkle_trees_collision_resistance.sp` for the merkle tree
  case-study in the concrete setting.
- `merkle_trees_perfect_hash_exact.sp` for an exact variant of the
  merkle tree case-study assuming a perfect (collision-free) hash
  function.
- `yubikey_concrete.sp` is an adaptation of the YubiKey case-study from
  [1] to the concrete setting.
- the original YubiKey case-study, in the asymptotic setting, can
  be found in `../stateful/yubikey.sp`.


## Bibliography

[1] David Baelde, Stéphanie Delaune, Adrien Koutsos, Solène Moreau:
    Cracking the Stateful Nut: Computational Proofs of Stateful
    Security Protocols using the Squirrel Proof Assistant.
    CSF 2022: 289-304

