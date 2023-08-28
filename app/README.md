# Experimental Squirrel in JS with CodeMirror editor

## Install instructions

Update and install `opam` packages :
It may asks you to install `libev-devel` with your OS's package-manager.

In the root directory of Squirrel :
```bash
opam update
opam install . --deps-only
opam install js_of_ocaml js_of_ocaml-tyxml ppx_deriving_yojson dream
```

Should have `js_of_ocaml >= 5.2.0` here.

Then you need to install `npm` dependencies with,
in the `app/` directory :
```bash
npm install .
```

For that you need `node` to [be installed](https://docs.npmjs.com/downloading-and-installing-node-js-and-npm).

## Build and Run

To build squirrel then run the server on `localhost:8080`.
In root directory of Squirrel :
```bash
make; make start
```

Then visit [http://localhost:8080](http://localhost:8080)…

## Usage

At this point only `ctrl-enter`, `ctrl-↑`, `ctrl-↓`  (resp. exec to
cursor, undo, exec next sentence commands) are bound.
