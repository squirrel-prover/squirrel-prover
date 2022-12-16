include Symbols.Channel

module L = Location

(*------------------------------------------------------------------*)
type channel = ns Symbols.t
type t = channel

let declare table s = fst (declare_exact table s ())

let pp_channel ppf c =
  (Printer.kws `ProcessChannel) ppf (Symbols.to_string c)

(*------------------------------------------------------------------*)
type p_channel = string Location.located
    
(*------------------------------------------------------------------*)
