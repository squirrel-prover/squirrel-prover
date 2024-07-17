open Utils

(*------------------------------------------------------------------*)
(** A printing environment *)
type ppenv = { dbg : bool; table : Symbols.table }

let default_ppe
    ?(dbg : bool option) ?(table : Symbols.table option) ()
  : ppenv
  =
  let dbg   = odflt false dbg in
  let table = odflt (Symbols.builtins_table ()) table in
  { dbg; table; }

(*------------------------------------------------------------------*)
(** A parametrized formatter *)
type 'a formatter_p = ppenv -> 'a formatter
