- **dependency and mutex lemmas**, [commit: `a5c01ceb`]

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

- **namespaces**, [commit: `6c37fe36`]
  
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


- **new syntax for system declaration**, [commit: `6c37fe36`, **breaking change**]

  ```
  system [foo] P
  ```

  should now be
  
  ```
  system foo = P
  ```
