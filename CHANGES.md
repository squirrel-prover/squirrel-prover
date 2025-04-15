### Support user-defined functions
  [commit: `543810eb`, **breaking change**]

Add support for user-defined functions which can use probabilistic
constructs, mutual recursion, system-dependency and pattern
matching. This generalizes the pre-existing notion of macros
(e.g. `frame@t, output@t`) that could only be defined through systems.

**Note (breaking change):** Supporting user-defined functions required
to adapt the mechanism dealing with recursion in cryptographic
reasoning tactics, in a way that may modify the behavior of said
tactics. Notably, generated subgoals may be different.

*A first example:*
Consider a system `Q` containing actions `A i` and `B j`. We can
define a function returning the index of the action using
```
let get_id @system:Q (u : timestamp) with
| A i when happens(u)    -> i
| B j when happens(u)    -> j
| init                   -> default0
| _ when not (happens u) -> default1.
```

*Pattern-matching:*
User-defined functions can optionally be defined using
pattern-matching, as above. A valid pattern-matching definition must be
exhaustive and use mutually exclusive cases. An automated procedure tries
to verify both conditions. If that procedure fails, these properties
must be established by the user manually.

*Unfolding:*
Unfolding of functions is done at the level of
patterns. E.g. `rewrite /get_id` will unfold a term `get_id t` into
one of the four cases of `get_id`'s definition, assuming the `when`
pattern conditions can be automatically discharged.

The tactic `expand ~def function_name` forces the unfolding of a function
into its full definition (using conditionals for the `when` conditions
and quantifiers for variables bound by each case). For example, this
allows proving lemmas that depend on `exec@tau` for a non-instantiated
`tau`, see `theories/Classic.sp`.

*Recursion:*
Functions can be recursive:
```
let rec fac (x : int) = if x <= 0 then 1 else x * fac (x - 1).
```
Termination of recursive functions must be proved by the user. By
default, Squirrel uses the generic well-founded order `<` over the
arguments.

Functions can be mutually recursive and system dependent. Further, the
termination order can be manually specified using the `termination_by
d` syntax, where `d` is a decreasing quantity.  Here is an example
relying on these features, where we manually give alternative
definitions of the `frame/output/state` macros (we omitted most
pattern-matching bodies):
```
let rec my_output @system:P t with
| A i when happens t -> ...
| init -> ...
| _ when not (happens t) -> ...
termination_by (t,1)

and stA i with
| _ when not(happens(A i)) -> ...
| null_i when happens (A null_i) -> ...
| _ when (happens (A i) && i <> null_i)-> ...
termination_by (A i,0)

and my_frame t with
| t when happens t && t<> init -> <my_frame (pred t), my_output t>
| init -> empty
| _ when not (happens t) -> empty
termination_by (t,2).
```

*More examples:*
Detailed examples can be found in `tests/ok/`:
 * `let-macro.sp`
 * `macro-let-rec.sp`
 * `macro-let-rec-crypto.sp`
 

*Details for developers:*
See `macros.mli` for the new definition of recursive functions. Most
of the code outside of `Macros` deals with user-defined functions in a
uniform fashion using the `Macros`'s API. We should gradually get rid
of specific treatments of the old macros `input`, `frame`, relying on
the generic mecanism instead.
 
The generalization of recursive definitions leads to an increased
number of occurrences finding and macro unfolding. This impacts
performance, but the update paves the way for a better treatment of
direct/indirect occurences.


### smt update
  [commit: 9655f18c] 

SMT tactic updated to rely on why3 1.8.

Improved the handling of polymorphic and higher-order terms. 
They don't crash smt anymore thanks to an opaque translation.

Support for the translation of squirrel's integers. 

Syntax update: the timeout for smt is defined with the optional 
integer argument ~timeout.

### reification of terms
  [commit: `04a01497`]

Added support for the reification of terms:
- the syntax |"t"| allows to reify a term t.
- Reified terms print as {"t"} to avoid any confusion (otherwise, different terms could be printed the same way).
- Add flag "prettyPrintReify" to controlling the pretty-printing of reified terms (toggled by default).


### library re-organisation
  [commit: `52d4a8a7`, **breaking change**]

Standard libraries have been reorganized. 

Most projects should start by including the `Core` library file
(instead of `Basic`, which has been removed).


### system variables
  [commit: `3a05f18b`]

Lemmas and axioms can now be parameterized by systems, bringing a form
of system parametricity: system arguments are inferred during lemma's
applications, as for type variables.

System variable binders are written using `{S1,...,Sn:system}`, or
equivalently `{S1:system} ... {Sn:system}`. Further, constraints can
be attached to a system variable. E.g. `{S : system[pair]}` requires
that `S` is a system pair.

Here are a few examples of the new syntax:
```
global lemma foo {P : system} {Q : system[pair]} @set:P @pair:Q {a, b : type} x y : ...
global lemma foo {P : system[pair]} @system:P {a, b : type} x y : ...
```
the latter being equivalent to
```
global lemma foo {P : system[pair]} @set:P @equiv:P {a, b : type} x y : ...
```

Additional changes:
- Replace brackets by parentheses to enclose system expressions.
  Further, remove the need to enclose system expressions in between
  parentheses when there are no parsing ambiguities.
  E.g. we can now do `print system P` (rather than `print P`).

- `any` is now syntactic sugar:
  + `lemma foo @system:any` is `lemma foo {P : system} @system:(set:P; equiv:None)`
  + `global lemma foo @system:any` is 
    `global lemma foo {P : system} {Q : system[pair]}  @system:(set:P; equiv:Q)`

- Allow to implicitly introduce system variable when giving a
  lemma's system context. E.g. the following two lemmas are equivalent:
  ```
  global lemma foo {P : system} {Q : system[pair]} @set:P @pair:Q : ...
  global lemma foo @set:'P @equiv:'Q
  ```
  Remark that because `'Q` occurs in an `@equiv` annotation, it is
  implicitly tagged with `pair`.

- Systems arguments can be manually provided using `A{S1,...,Sn}`,
  where `A` is a lemma parameterized by `n` systems and `S1,...,Sn` are
  system expressions.

### basic builtin support for integer and string constants
  [commit: `7542e89e`]

Added builtin support for integer and string constants. E.g.
```
op x : int = 42.
op s : string = "42".
lemma [any] _ : x + 42 = 84 && s = "42".
```
There is also basic support for integer computations in the reduction engine
(e.g. `21+21` reduces to `42`).
  
### better automated reasoning on action dependencies
  [commit: `3280faaa`]

Improved the automated reasoning w.r.t. action dependencies.
Impacts `constraints` (and thus `auto`), as well as some automated
reasoning used to determine whether an action happens before
unrolling a macros.

### syntax change for memory cells
  [commit: `5b2415c0b765`, **breaking change**]

States update accepted non currified inputs, which lead to
inconsistent notations in process declaration such as:
```
rK(i,j) := <rK i j, rK i j>;
```
The expected syntax is now 
```
rK i j := <rK i j, rK i j>;
```


### syntax change for global formulas
  [commit: `71c81505`, **breaking change**]
  
A modification of the syntax of global formulas created a few syntax changes:

- ambiguities in some commands must now be manually resolved.
  + `have ip : any_form` becomes `have ip : local_form` or
    `ghave ip : global_form`
  + `search any_form` becomes `search local_form`, 
    `search local(local_form)` or `search global(global_form)`

- localizing a proof-term `pt` is now done by writing `localize(pt)`,
  rather than `%local(pt)`.

### type arguments
  [commit: `4202b3e3`]

Type arguments of symbols can now be manually provided by writing
`s[ty1, ..., tyn]` when `s` is a symbol with `n` arguments.
E.g. `witness[message]` is the symbol `witness` of type `message`.

The same syntax can be used to instantiate the type arguments of a
lemma in a proof-term.

### arguments for s_items
  [commit: `4202b3e3`, **breaking change**]

The syntax to provide named arguments to `s_item` such as `//`,
`/=`, etc, has been changed from `[// ~arg1:foo ~arg2 ...]` to 
`` `[// ~arg1:foo ~arg2 ...]`` (a backtick must now precede the 
opening bracket).

### dependency and mutex lemmas
  [commit: `a5c01ceb`]

Dependency and mutex lemmas are now generated for [any] systems.
Moreover, the form of dependency lemmas has been simplified:
when in the past we might have had
```
axiom [mysys] depends_mysys_A1_A2 :
  forall (tau:timestamp,i,j:index),
  tau = A2(i,j) =>
  happens(tau) => A1(i) < A2(j).
```
we now have
```
axiom [any] depends_A1_A2 :
  forall (tau:timestamp,i,j:index),
  happens(A2(i,j)) => A1(i) < A2(j).
```

### namespaces
  [commit: `6c37fe36`]
  
Squirrel objects can now be stored in namespace, which allow to
organize developments. For example,

```
namespace Int.
  type int.
  op (+) : int -> int -> int.
end Int.

namespace Real.
  type real.
  op (+) : real -> real -> int.
end Real.
```

Defines two operators both with the same short name `+` but with
different long names `Int.+` and `Real.+` (a long named is called a
qualified name).

Then, if you open the namespaces by doing `open Int. open Real`, you
can use the short name `+`, and Squirrel will automatically use
`Int.+` or `Real.+` depending on its arguments.


### new syntax for system declaration
  [commit: `6c37fe36`, **breaking change**]

```
system [foo] P
```

should now be

```
system foo = P
```
