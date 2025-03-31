# Squirrel Prover, SMT article examples

This folder contains the files for the examples and case studies in the SMT article submitted
at CSF 2025.

## Axioms list

`axioms-core.sp` contains a list of the axiom included in the Why3 theory given to the SMT solvers. 

## Canauth variations

A simplified version of the protocol CANAuth (`examples/stateful/canauth.sp`) was detailed in the article.
We give two version of this protocol, one using an abstract type for the counter in `canauth-simpl.sp` (without smt solvers) 
and `canauth-simpl-smt.sp` (with smt solvers) and one using integers in `canauth-int.sp` (with smt solvers).

## Stateful protocols

Protocols from the folder `examples/stateful` had their proof simplified using smt solvers. These new proofs 
are in the following files : 
- `canauth-smt.sp`
- `running-ex-oracle-smt.sp`
- `running-ex-smt.sp`
- `slk06-smt.sp`
- `toy-counter-smt.sp`
- `yplrk05-smt.sp`
- `yubihsm-smt.sp`
- `yubikey-smt.sp`
