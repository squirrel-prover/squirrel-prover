# Contribute.md

## Documentation

The documentation for developers may be built with `make doc`. The standard ocamldoc syntax should be used for comments.
Comments for functions should be put inside the `.mli` files.

## Coding conventions

* 80 characters lines
* rather use begin end than parenthesis inside if blocks
* if a let construct goes for multiple line, the `in` should be on a new line at the end.

Good: 
```
let x =
	...
   in
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
```
Bad:
```
type t =
  Toto
 | Tutu
```
