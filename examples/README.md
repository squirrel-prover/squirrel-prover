# Squirrel Prover Examples

This folder contains the examples and case studies of the Squirrel Prover.

## Running Examples

The running examples of the original paper [1] correspond to the files:
- `running-ex-auth.sp` for the authentication property
- `basic-hash.sp` for the complete proof of unlinkability
They are well suited to get a first feel of the tool, as well as the tutorial files in `tutorial/`.

## Comparison with CryptoVerif and EasyCrypt
To help comparing Squirrel to existing approaches in the computational model, we conduct the security analysis of the same protocol (Basic Hash) in three different tools: Squirrel, CryptoVerif and EasyCrypt.

The corresponding files can be found in:
- `basic-hash.sp` authentication and unlinkability, Squirrel
- `cryptoverif/basic-hash-auth.pcv` authentication, CryptoVerif
- `cryptoverif/basic-hash-unlink.pcv` unlinkability, CryptoVerif
- `easycrypt/basic-hash-auth.pcv` authentication, EasyCrypt
- `easycrypt/basic-hash-unlink.pcv` unlinkability, EasyCrypt

## Original Case Studies

Case studies that use an axiom among `cca1`, `enckp`, `intctxt`, `prf`, `euf`, `ddh`, `xor`
can be found with:
```
$ grep "AXIOMNAME " *.sp
```

The case studies of [1] can be split into multiple categories.
For each protocol, we provide the
bibliographic reference that contains the description we used to model the
protocol, which may differ from the original specification of the protocol.

### RFID Based

Basic Hash [A]:
- `basic-hash.sp`

Feldhofer [B]:
- `feldhofer.sp`

Hash Lock [C]:
- `hash-lock.sp`

LAK [D]:
- `lak-tags.sp`

MW [E]:
- `mw.sp`
- `mw-full.sp`

### Encryption Based

Private Authentication [F]:
 - `private-authentication.sp`

### DDH Based

Signed DDH key exchange, ISO 9798-3 [G]
 - `signed-ddh.sp`
 - `signed-ddh-compo.sp`

SSH protocol with forwarding agent [H]
 - `ssh-forward-part1-compo.sp`
 - `ssh-forward-part2-compo.sp`

### Composition

The case studies that end with the `-compo` suffix leverage the composition
result of [H]. They correspond to proofs that are performed for a single
session, but that allow to derive thanks to the theorems of [H] a security
guarantee for an unbounded number of sessions.


## Post-quantum Soundness

An option allows to check if a proof is sound for quantum attackers. It is enabled inside a file with:
`set postQuantumSound = true.`


The examples of protocols designed to be post-quantum are inside the `postQuantumKE/` subfolder. though, other case-studies have been verified to be post quantum sound, and a list can be extracted with a `grep` over the flag.

### KEM based

Generic construction from [I]:
 - `kemKE_BCGNP.sp`

Generic construction (more complex) from [J]:
 - `kemKE_FSXY.sp`

Generic PQ construction of X3DH like [O] :
 - `PQ-xrdh-like.sp`

### PRF based

IkeV1 with pre-shared keys for authentication [L]:
 - `ikeV1_psk.sp`
 IkeV2 signed with pre-shared keys [M,N]:
 - `ikeV2_sign.sp`


## Post-quantum soundness

All but the DDH based examples in this repository are post-quantum sound.

## BC Bibliography

 - [1] David Baelde, Stéphanie Delaune, Adrien Koutsos, Charlie Jacomme, Solène Moreau (2021). An interactive prover for protocol verification in the computational model. IEEE Symposium on Security and Privacy (S&P'21).

## Bibliography

 - [A] Mayla Brusò, Kostas Chatzikokolakis, and Jerry den Hartog. Formal
Verification of Privacy for RFID Systems. pages 75–88, July 2010.
 - [B] Martin Feldhofer, Sandra Dominikus, and Johannes Wolkerstorfer.
Strong authentication for RFID systems using the AES algorithm. In
Marc Joye and Jean-Jacques Quisquater, editors, Cryptographic
Hardware and Embedded Systems - CHES 2004: 6th International Workshop
Cambridge, MA, USA, August 11-13, 2004. Proceedings, volume 3156
of Lecture Notes in Computer Science, pages 357–370. Springer, 2004.
 - [C] Ari Juels and Stephen A. Weis. Defining strong privacy for RFID. ACM
Trans. Inf. Syst. Secur., 13(1):7:1–7:23, 2009.
 - [D] Lucca Hirschi, David Baelde, and Stéphanie Delaune. A method for
unbounded verification of privacy-type properties. Journal of Computer
Security, 27(3):277–342, 2019.
 - [E] David Molnar and David A. Wagner. Privacy and security in library
RFID: issues, practices, and architectures. In Vijayalakshmi Atluri,
Birgit Pfitzmann, and Patrick D. McDaniel, editors, Proceedings of the
11th ACM Conference on Computer and Communications Security, CCS
2004, Washington, DC, USA, October 25-29, 2004, pages 210–219.
ACM, 2004.
 - [F] G. Bana and H. Comon-Lundh. A computationally complete symbolic
attacker for equivalence properties. In 2014 ACM Conference on
Computer and Communications Security, CCS ’14, pages 609–620.
ACM, 2014.
 - [G] ISO/IEC 9798-3:2019, IT Security techniques – Entity authentication –
Part 3: Mechanisms using digital signature techniques.
 - [H] Hubert Comon, Charlie Jacomme, and Guillaume Scerri. Oracle
simulation: a technique for protocol composition with long term shared secrets.
In Jonathan Katz and Giovanni Vigna, editors, Proceedings of the 27st
ACM Conference on Computer and Communications Security (CCS’20),
Orlando, USA, November 2020. ACM Press.
 - [I] Boyd, Colin and Cliff, Yvonne and Nieto, Juan M. Gonzalez and Paterson, Kenneth G. One-round key exchange in the standard model.
 - [J] Fujioka, Atsushi and Suzuki, Koutarou and Xagawa, Keita and Yoneyama, Kazuki. Strongly Secure Authenticated Key Exchange from Factoring, Codes, and Lattices
 - [L] Internet Key Exchange Version 1, RFC2409 https://datatracker.ietf.org/doc/html/rfc2409
 - [M] Internet Key Exchange Version 2, RFC7296 https://datatracker.ietf.org/doc/html/rfc7296
 - [N] Mixing Preshared Keys in (IKEv2) for Post-quantum Security, RFC8784 https://datatracker.ietf.org/doc/html/rfc8784
 - [O] Keitaro Hashimoto,Shuichi Katsumata, Kris Kwiatkowski, Thomas Prest. An Efficient and Generic Construction for Signal’s Handshake (X3DH): Post-Quantum, State Leakage Secure, and Deniable.
