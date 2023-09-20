type T.

abstract g : T -> bool.
abstract f : message -> T.

channel c.

process foo = 
  in(c,x); 
  let x = f x in

  !_i ( 
    in(c,vote);

    if g x then
      out(c,empty)
  ).

system foo.
