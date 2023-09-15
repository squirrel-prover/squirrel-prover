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

## Generate `jsquirrel.zip`
To generate a standalone jsquirrel in zip you can,
in root directory of Squirrel :
```bash
make zipsquirrel
```

The zip file is in _build/default/app/jsquirrel.zip

# How to use `jsquirrel` from zip file

First unzip `jsquirrel.zip` anywhere you want with
```bash
unzip jsquirrel.zip
```

Then go in the newly extracted `www` directory and serve with your
favorite light server like `python http.server`
```bash
cd www; python3 -m http.server
```

This should serve `jsquirrel` into `localhost:8000` by default.
Open your browser at `localhost:8000`…

## Usage

At this point only `ctrl-enter`, `ctrl-↑`, `ctrl-↓`  (resp. exec to
cursor, undo, exec next sentence commands) are bound.

`ctrl-o` will open/close a dialog to open a file. `ctrl-s` will open/close a
dialog to save the file.
