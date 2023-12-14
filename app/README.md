# Experimental Squirrel in JS with CodeMirror editor

## Install instructions

You first need to update and install `opam` packages, by running the following
from the root directory of the Squirrel repository:
```bash
opam update
opam install . --deps-only
opam install js_of_ocaml js_of_ocaml-tyxml ppx_deriving_yojson dream
```
It may ask you to install `libev-devel` with your OS's package-manager.

This should install `js_of_ocaml >= 5.2.0`.

Then you need `node` to [be installed](https://docs.npmjs.com/downloading-and-installing-node-js-and-npm).

Finally, install `npm` dependencies by running,
from the `app/` subdirectory:
```bash
npm install .
```

## Build and Run

To build squirrel then run the server on `localhost:8080`.
In root directory of Squirrel :
```bash
make start
```

## Generate `jsquirrel.zip`

To generate a standalone jsquirrel in zip you can run,
from the root directory of Squirrel :
```bash
make zipsquirrel
```

The zip file is in `_build/default/app/jsquirrel.zip`.

# How to use `jsquirrel` from zip file

First unzip `jsquirrel.zip` anywhere you want:
```bash
unzip jsquirrel.zip
```

Then go in the newly extracted `www` directory and serve with your
favorite light server like `python http.server`:
```bash
cd www && python3 -m http.server
```

This should serve `jsquirrel` into `localhost:8000` by default.
Open your browser at `http://localhost:8000`…

## Usage

The following keyboard shortcuts are available:

| Mapping          | Action                               |
| ---              | ---                                  |
| `ctrl-enter`     | execute until cursor                 |
| `ctrl-↑/k`       | undo                                 |
| `ctrl-↓/j`       | execute next sentence                |
| `ctrl-shift-↑/↓` | move focus                           |
| `ctrl-s`         | open/close a dialog to save the file |
| `ctrl-S`         | save the file in disk                |

See the help (?) provided.
