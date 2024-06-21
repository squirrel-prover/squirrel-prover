system null.

namespace A.
  namespace B.
    op a = empty.
  end B.
end A.

namespace C.
  axiom _ : A.B.a = empty.
  open A.
  (* B resolves to [A.B] because [A] was brought in scope *)
  open B. 
  axiom _ : a = empty.
end C.
