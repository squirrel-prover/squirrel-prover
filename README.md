# MetaBC prover


## Build

You need OCaml. Developers use versions 4.05 and 4.06. The software
should build with versions up to 4.08, but with deprecation warnings.
You need the following tools and libraries, to be installed e.g.
with opam.
```
$ opam install . -y --deps-only
```

You should then be able to build the software. The default target
builds the prover and testing binaries and runs tests:
```
$ make
```

You can also just build the prover with `make metabc`, test with
`make test`.

The documentation for developers may be built with `make doc`.

## Use

### Standalone

You can check a proof development by simply passing the file to `metabc`:
```
$ ./metabc examples/euf.mbc
```

### With proof general

The required `.el` files are inside the `utils` folder. The `metabc.el` file
contains comments detailing the installation of metabc for ProofGeneral.
We recommend installing ProofGeneral from the git repository.

## Quick guide

MetaBC developments are conventionally written in `.mbc` files. They start
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
term <id>(<args>) : <msg_type> = <term>            (* macro definition *)
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

### Lemmas

TODO: axioms, goals, proofs, available tactics

## Developper details
 
# Documentation

It can be generated through:
```
$ make doc
```
The documentation can then be browsed through `metabc.docdic/index.html`.

# Coverage
It can be generated through:
```
$ make coverage
```
The documentation can then be browsed through `_coverage/index.html`.

