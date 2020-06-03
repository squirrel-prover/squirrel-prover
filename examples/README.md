# Squirrel Prover Examples

This folder contains the examples and case studies of the Squirrel Prover paper.

## Running Examples

The two running examples of the paper are `running-ex-axiom.sp` and
`running-ex.sp`. They are well suited to get a first feel of the tool.

## Case Studies

All the other `.sp` files correspond to a case study of the paper. The folder
`wip/` contains some work in progress examples, i.e. examples that are not
complete. The folder `demo/` contains some basic files that can be used to give
a live demonstration of the tool.

Case studies that end with the `-light` suffix are simplified models of the
protocols, that omit the last check.

Case studies that use an axiom among `cca1`,`enckp`,`prf`,`euf`,`ddh`
can be found with:
```
$ grep "AXIOMNAME " *.sp
```

The case studies can be split into multiple categories. We provide the
bibliographic reference that contains the description we used to model the
protocol, which may differ from the original specification of the protocol.

### RFID Based

Basic Hash [A]:
- basic-hash.sp

Feldhofer [B]:
- feldhofer-light.sp

Hash Lock [C]:
- hash-lock.sp

LAK [D]:
- lak-tags-light.sp

MW [E]:
- mw-light.sp
- mw.sp

### Encryption Based

Private Authentication [F]:
 - private-authentication-light.sp

### DDH Based

Signed DDH key exchange, ISO 9798-3 [G]
 - signed-ddh.sp
 - signed-ddh-compo.sp

SSH protocol with forwarding agent [H]
 - ssh-forward-part1-compo.sp
 - ssh-forward-part2-compo.sp


### Composition

The case studies that end with the `-compo` suffix leverage the composition
result of [H]. They corresponds to proofs that are performed for a single
session, but that allow to derive thanks to the Theorems of [H] the security for
an unbounded number of sessions.

## Bibliography

 - [A] Mayla Brusò, Kostas Chatzikokolakis, and Jerry den Hartog. Formal
Verification of Privacy for RFID Systems. pages 75–88, July 2010.
 - [B] Martin Feldhofer, Sandra Dominikus, and Johannes Wolkerstorfer.
Strong authentication for RFID systems using the AES algorithm. In
Marc Joye and Jean-Jacques Quisquater, editors, Cryptographic Hard-
ware and Embedded Systems - CHES 2004: 6th International Workshop
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
 - [H] Hubert Comon, Charlie Jacomme, and Guillaume Scerri. Oracle simula-
tion: a technique for protocol composition with long term shared secrets.
In Jonathan Katz and Giovanni Vigna, editors, Proceedings of the 27st
ACM Conference on Computer and Communications Security (CCS’20),
Orlando, USA, November 2020. ACM Press. To appear
