# Squirrel Prover

## Build

You need OCaml version 4.10 or more (tested up to 4.13.1).

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

### Installing the Proof General mode for Emacs (optional, recommanded)

The required `.el` files are inside the `utils` folder. 
We recommend installing Proof General from the git repository.


- 0. Clone the git repository of proof general inside your `~/.emacs.d/lisp`:
```
mkdir -p ~/.emacs.d/lisp/ && cd ~/.emacs.d/lisp/
git clone https://github.com/ProofGeneral/PG
```

- 1. Create a squirrel sub-directory:
```
mkdir -p ~/.emacs.d/lisp/PG/squirrel
```

- 2. Copy and paste this file, and `squirrel-syntax.el` inside it:
```
cp squirrel.el squirrel-syntax.el ~/.emacs.d/lisp/PG/squirrel
```

- 3. Moreover, in the file `~/.emacs.d/lisp/PG/generic/proof-site.el`,
   add to the list `proof-assistant-table-default` the following line:
```
 (squirrel "squirrel" "sp")
```
Then erase the outdated compiled version of this file:
```
rm ~/.emacs.d/lisp/PG/generic/proof-site.elc
```

- 4. Run the following command to configure emacs:
```
echo -e "(require 'ansi-color)\n(load \"~/.emacs.d/lisp/PG/generic/proof-site\")" >> ~/.emacs
```

5. Run emacs from the squirrel repository on some example file,
with the squirrel repository in the path:
```
export PATH=$PATH:/path/to/squirrel
emacs examples/<file>.sp
```

### Dependencies for the `smt` tactic (optional)

(If those dependencies are not installed, Squirrel will still compile, but the
`smt` tactic won't work. You will need to recompile Squirrel *after* the `why3`
package has been installed.)

First install Why3 and Alt-Ergo using opam:
```
$ opam install why3 alt-ergo
```

This also installs the Why3 OCaml library used by Squirrel.

Then tell Why3 to automatically detect that Alt-Ergo is installed and update its
configuration accordingly:
```
$ why3 config detect
```

Why3 is also able to find SMT solvers installed using the system package manager
(e.g. `sudo dnf install z3` on Fedora) but those aren't supported by our code
yet.

## Use

### Standalone

You can check a proof development by simply passing the file to `squirrel`:
```
$ ./squirrel examples/basic-hash.sp
```
or using Emacs with the Proof General mode (if installed)
```
$ emacs examples/basic-hash.sp
```

## Examples
Examples of developments in Squirrel can be found in:
- `examples/`

Those include classical and post-quantum sound proofs of protocols.
See `examples/README.md` for details.

## Quick guide

For a first introduction to the syntax, we recommend to open with ProofGeneral
the `examples/tutorial/tutorial.sp`, that provides a run through of the syntax
with executables snippets. Then, browsing the `examples` folder should provide a
wide variety of examples, starting e.g. with `basic-hash.sp`.

As a next step, a more advanced tutorial is available in
`examples/tutorial/tutorial-avanced.sp`.

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

Declarations blocks are delimited with a `.`, which defines the next bunch of
code that will be processed by Squirrel.

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

Finally, the system under study is declared:
```
system <process>.
```

The system can be given an explicit name using the following syntax,
which is necessary when multiple systems are used in the same file:
```
system [NAME] <process>.
```

### Axioms, lemmas and proofs

Axioms can be declared using the "axiom" keyword:
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

We refer the reader to `CONTRIBUTING.md` for coding conventions.

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
