include Core.

namespace String.
  op ( + ) : string -> string -> string.

  axiom [any] add_assoc : assoc ( + ).
end String.
