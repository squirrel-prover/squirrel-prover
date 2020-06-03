# Contribute.md

## Documentation

The documentation for developers may be built with `make doc`. The standard ocamldoc syntax should be used for comments.
Comments for functions should be put inside the `.mli` files.

New modules should be added to `squirrel.odocl`.

## Coding conventions

* 80 characters lines
* use `begin/end` than parenthesis to delimit block:
```
if .. then begin
end

begin match .. with
  | ...
end
```
* do not indent after `let`:
```
let x = ... in
let y = ... in
do something
```
* if a let construct spans across multiple line, it should be indented and the `in` should be on a new line at the end:

Good:
```
let x =
  ...
in
...
```
Bad:
```
let x =
  ...  in
```
* always put | for the first pattern matching definitions:

Good:
```
type t =
  | Toto
  | Tutu

match .. with
  | Toto -> ...
  | Tutu -> ...
```
Bad:
```
type t =
    Toto
  | Tutu
match .. with
    Toto -> ...
  | Tutu -> ...
```
* in `mly` files, the `x=TOTO` notation should not have spaces
