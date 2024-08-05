One can use the `ocamldebug` utility to run squirrel in debug mode.

First, build the byte version with `dune build squirrel.bc`.

Then, start the ocamldebug shell with 
`ocamldebug -I _build/default/src/core/.squirrelcore.objs/byte/  _build/default/squirrel.bc `.

This only initializes ocamldebug squirrel, we must specify an input file with: `set arguments path/to/mycoolfile.sp`

Now, a few useful commands inside ocamldebug shell are:
 * `run` -> launches the squirrel execution on the file
 * ctrl+c -> interrupt the execution
 * `break @ Squirrelcore__Module line` insert a break point inside the Module module file at line x.
 * `start` run until next break point
 * `previous` go back in time until next break point
 
When at a program point, we can:
 * `backtrace` -> display the current backtrace
 * `frame` -> display the current line to be executed 
 * `print v` -> print the value of the ocaml variable v
 * `next` and `previous` go backward and forward one step

