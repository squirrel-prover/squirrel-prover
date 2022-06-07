

channel c

abstract tobool : message -> boolean

name n : index -> message

process A (i:index, m:message) = 
  in(c,x);
  if i = i && m = zero then
    out(c,n(i)) 
  else
    let a = if true = tobool(x) then zero else zero in
  out(c,n(i))

system !_i0 A(i0, diff(zero,zero)).
