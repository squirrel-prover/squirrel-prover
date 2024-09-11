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

### type argument
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
