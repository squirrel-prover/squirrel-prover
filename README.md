# Squirrel Prover


## Build

You need OCaml version 4.10 or more.

We recommend that you use opam (version 2.0 or more). It will notably allow
you to install the required tools and libraries, with the following command
inside this directory:
```
$ opam install . -y --deps-only
```

You should then be able to build the software. The default target
builds the prover and testing binaries and runs tests:
```
$ make
```

You can also just build the prover with `make squirrel`, test with `make test`.

The documentation for developers may be built with `make doc`.

## Use

### Standalone

You can check a proof development by simply passing the file to `squirrel`:
```
$ ./squirrel examples/basic-hash.sp
```

### With proof general

The required `.el` files are inside the `utils` folder. The `squirrel.el` file
contains comments detailing the installation of squirrel for ProofGeneral.
We recommend installing ProofGeneral from the git repository.

## Examples
Examples of developments in Squirrel can be found in:
- `examples/`

## Quick guide

Squirrel developments are conventionally written in `.sp` files. They start
with a system description, followed by some lemmas corresponding to trace
properties.

Comments are noted `(* in this way *)`.

### System description

#### Messages

Terms can be of type `message`, `boolean`, `index` and `timestamp`.
The first two are message kinds, respectively corresponding to a bitstring
of length the security parameter, and a single bit. Indices are used to
have infinite collections of objects, and timestamps are used in the
meta-logic.

You can declare new term constructors, with identifier `id`,
of the following kinds, where `msg_type` is either `message` or
`boolean`, and `args` is a comma-separated list of typed variables,
e.g. `x:boolean` or `i:index`:
```
hash <id>                                          (* keyed hash function *)
name <id> : index -> .. -> index -> message        (* indexed name *)
mutable <id> : index -> .. -> index -> <msg_type>  (* indexed memory cell *)
```

#### Processes

Processes are then declared as follows, using previously declared channels:
```
channel <id>
process <id>(<args>) = <process>
```
The syntax of processes is similar to the one used in ProVerif. New
names can be introduced inside processes: they will be transformed into
toplevel declarations (indexed as necessary) when the model is ingested
by the prover. Replications are indexed, written `!_i <process>`, to
be able to refer to their copies.

#### System

Finally, the system under study is declared. Note the period (`.`) that
terminates this statement:
```
system <process>.
```

The system can be given an explicit name using the following syntax,
which is necessary when multiple systems are used in the same file:
```
system [NAME] <process>.
```

### Axioms, lemmas and proofs

Axioms can be declared in the prologue using the "axiom" keyword:
```
axiom NAME : <formula>.
```
Note that an axiom can only be declared after the corresponding system
has been declared.

Axioms can be declared for a specific system, rather than the default
one:
```
axiom [SYSTEM_NAME] GOAL_NAME : <formula>.
```

Reachability goals are noted as follows:
```
goal NAME : <formula>.
```

By default, a goal is expressed simultaneously for the two projections
of the system. In such cases, it is often the case that, at some point
in the proof, one needs to use the `project` tactic to handle separately
the two sides.

Alternatively, goals can be stated wrt a specific side of the system:
```
goal [left/right/none,SYSTEM_NAME] GOAL_NAME : <formula>.
```

Goals are proved using tactic-based proof scripts. Proofs start with
`Proof` and end with `Qed`. The special tactic `help` can be used to
obtain a list of all available tactics (for reachability or equivalence
goals, depending on the context).

## Developper details

# Documentation

It can be generated through:
```
$ make doc
```
The documentation can then be browsed through `squirrel.docdic/index.html`.

# Coverage
It can be generated through:
```
$ make coverage
```
The documentation can then be browsed through `_coverage/index.html`.
