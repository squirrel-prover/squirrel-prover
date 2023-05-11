# Experimental Squirrel in JS with CodeMirror editor

## Install instructions

Update and install `opam` packages :
It may asks you to install `libev-devel` with your OS's package-manager.

```bash
opam update
opam install . --deps-only
```

Should have `js_of_ocaml >= 5.2.0` here.

Then you need to install `npm` dependencies with:

```bash
npm install .
```

For that you need `node` to [be installed](https://docs.npmjs.com/downloading-and-installing-node-js-and-npm).

## Build and Run

To build squirrel then run the server on `localhost:8080` :

```bash
make; make start
```

Then visit [http://localhost:8080](http://localhost:8080)…

## Usage

At this point only `ctrl-enter` (exec to cursor command) is bound.
You dans execute sentences and retract script by modifying previous
sentences.
