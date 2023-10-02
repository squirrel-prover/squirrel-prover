channel c.

type t.

abstract f : message * message.

process P =
  let x = f in
  out(c, x # 1).
