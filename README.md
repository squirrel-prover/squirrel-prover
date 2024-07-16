# Squirrel Prover

The Squirrel Prover is a proof assistant dedicated to the verification
of cryptographic protocols. It relies on a higher-order probabilistic
logic following the computationnally complete symbolic attacker
approach, and provides guarantees in the computational model.

## Try it

Online version of `Squirrel` is available with a complete tutorial
[here](https://squirrel-prover.github.io/jsquirrel/?open=0-logic.sp).

You can find more examples in the `examples` directory.

## Reference Manual

The manual is available online
[here](https://squirrel-prover.github.io/documentation/).

For more information, the presentation site is on
[github.io](https://squirrel-prover.github.io/).

## Installation

Squirrel dependencies can be easily installed using Opam (version 2.0
or more). 

### Installing Opam

If you do not yet have Opam, it can be installed as follows:
- On Debian/Ubuntu
  
  ```
  apt-get install ocaml opam
  ```
  
- One MacOSX
  
  ```
  brew install ocaml opam
  ```
  
- otherwise, opam installation instructions are available
  [here](https://opam.ocaml.org/doc/Install.html).

### Building Squirrel

1. Switch to a dedicated compiler for Squirrel 
  
   ```
   opam switch create squirrel 5.1.1
   ```

2. Optionally, pin-it to the local repository
   
   ```
   opam switch link squirrel .
   ```
   
3. Initialize you environment variables:
   
   ```
   eval $(opam env)
   ```

4. Install Squirrel dependencies:
   
   ```
   opam install . -y --deps-only
   ```
   
5. You should then be able to build the software. The default target
   builds the prover and testing binaries and runs tests:
   
   ```
   make
   ```
   
   You can then run tests with `make test`.

   The documentation for developers may be built with `make doc`.

   The documentation for users may be built with `make refman-html`.

### Adding SMT support (optional)

SMT support can be added to Squirrel by installing the necessary
dependencies. If those dependencies are not installed, Squirrel will
still compile, but the `smt` tactic won't work. Note that you will
need to recompile Squirrel *after* the `why3` package has been
installed.

1. Install Why3, Alt-Ergo and Z3 using opam:
   
   ```
   opam install why3 alt-ergo z3
   ```

   This also installs the Why3 OCaml library used by Squirrel.

2. Then tell Why3 to automatically detect supported SMT provers and update its
   configuration accordingly:

   ```
   why3 config detect
   ```

3. Recompile Squirrel:
   
   ```
   eval $(opam env)
   make
   ```

### Installing the Proof General mode for Emacs (optional, recommended)

The required `.el` files are inside the `utils/` folder. 
We recommend installing Proof General from the git repository.


- Clone the git repository of proof general inside your `~/.emacs.d/lisp`:
  
  ```
  mkdir -p ~/.emacs.d/lisp/ && cd ~/.emacs.d/lisp/
  git clone https://github.com/ProofGeneral/PG
  ```

- Create a squirrel sub-directory:
  ```
  mkdir -p ~/.emacs.d/lisp/PG/squirrel
  ```

- Copy and paste this file, and `squirrel-syntax.el` inside it (creating
  symbolic links may be a better idea if you intend your config to follow
  the repository changes):
  
  ```
  cp squirrel.el squirrel-syntax.el ~/.emacs.d/lisp/PG/squirrel
  ```

- Moreover, in the file `~/.emacs.d/lisp/PG/generic/proof-site.el`,
   add to the list `proof-assistant-table-default` the following line:
  
  ```
   (squirrel "Squirrel" "sp")
  ```
  
  Then erase the outdated compiled version of this file:
  ```
  rm ~/.emacs.d/lisp/PG/generic/proof-site.elc
  ```

- Run the following command to configure emacs:

  ```
  echo -e "(require 'ansi-color)\n(load \"~/.emacs.d/lisp/PG/generic/proof-site\")" >> ~/.emacs
  ```

- Run emacs from the squirrel repository on some example file,
  with the squirrel repository in the path:
  
  ```
  export PATH=$PATH:/path/to/squirrel
  emacs examples/<file>.sp
  ```

### Unicode support in Emacs (Proof General) (optional)

If you are missing some Unicode fonts in Emacs, you can try installing the Symbola font.
For example, on a Debian distribution:

```
 apt-get install -y fonts-symbola 
```

should do the trick.


## Use

### Standalone

You can check a proof development by simply passing the file to `squirrel`:

```
./squirrel examples/basic-hash.sp
```

or using Emacs with the Proof General mode (if installed)

```
emacs examples/basic-hash.sp
```

## Examples

Examples of developments in Squirrel can be found in:

- `examples/`

See `examples/README.md` for details.

## Tutorial

For a first introduction to the syntax, we recommend to open with ProofGeneral
the `examples/basic-tutorial/tutorial.sp`, that provides a run through of the syntax
with executables snippets. Then, browsing the `examples` folder should provide a
wide variety of examples, starting e.g. with `basic-hash.sp`.

### Detailed Tutorial

A more complete tutorial is available in
```
examples/tutorial/
```

This tutorial consists in a series of exercises of increasing
difficulty, and covers the basic logical constructs and tactics
manipulating them, several cryptographic assumptions, accessibility
properties (authentication, injective authentication), equivalence
properties (unlinkability), stateful protocol, and protocol
composition.

- [0-logic](examples/tutorial/0-logic.sp)
- [1-crypto-hash](examples/tutorial/1-crypto-hash.sp)
- [2-crypto-enc](examples/tutorial/2-crypto-enc.sp)
- [3-hash-lock-auth](examples/tutorial/3-hash-lock-auth.sp)
- [4-hash-lock-unlink](examples/tutorial/4-hash-lock-unlink.sp)
- [5-stateful](examples/tutorial/5-stateful.sp)
- [6-key-establishment](examples/tutorial/6-key-establishment.sp)


## Developper details

We refer the reader to `CONTRIBUTING.md` for coding conventions.

# Visualisation and HTML export

### Data visualisation (with Proof General)

To have a graphical representation of the state of the proof,
set the variable `SP_VISU` to `ok` in your environnement.
Then, launch a Squirrel file with Emacs:

```
export SP_VISU=ok
emacs examples/basic-hash.sp
```

You need to validate at least one line in Emacs to launch the local server.
Then, you can access the visualisation at: [http://localhost:8080/visualisation.html](http://localhost:8080/visualisation.html)

### Export in HTML format (needs [pandoc](https://pandoc.org/))

To convert a Squirrel development to HTML, you need:

* A **Squirrel file** `PATH1/squirrel_name.sp`
* An **HTML template file** `PATH2/page.html` containing a line:
`<!--HERE-->` (without spaces or tabulations)

A default HTML template can be found at `scripts/html_export/page.html`.


```
./squirrel PATH1/squirrel_name.sp --html PATH2/page.html
```

The previous command will create a copy of `page.html` in the same directory pointed
by `PATH1` named `squirrel_name.html`. **Beware** that, if a file already
exists with this name, it will be deleted by this operation.

This new file will have the output of Squirrel formatted in HTML and placed
where the `<!--HERE-->` tag is.

Squirrel will put its results between span tags that will not be
displayed. This result can later be processed, with javascript for
example.

Each instruction in the Squirrel file is translated into an item
of the following form (with `_i` in the tags' id replaced by the number of the instuction):

```
<span class="squirrel-step" id="step_i">
  <span class="input-line" id="in_i">
    Input
  </span>
  <span class="output-line" id="out_i">
    Output
  </span>
  <span class="com-line" id="com_i">
    Comment
  </span>
</span>
```

The "Comment" part will be filled by comments in the Squirrel file
starting with `(**` and ending with `*)`.
It is possible to format these comment with pandoc's Markdown
(detailled [here](https://pandoc.org/MANUAL.html#pandocs-markdown)).
Others comments will be left in the "Input" part.

# Documentation

## Sphinx documentation

The user doc relies on the Sphinx framework.
See `documentation/sphinx/README.rst` for how to build and use.

## Developper documentation

The code's documentation can be generated through:
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

# JSquirrel

If you want to run `Squirrel` in your browser we've transpiled
Squirrel into JS using
[JSofOcaml](https://ocsigen.org/js_of_ocaml/latest/manual/overview)
linked to [CodeMirror6](https://codemirror.net/) editor.

See `app/README.md` for more.
