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
