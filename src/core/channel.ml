include Symbols.Channel

module L = Location

(*------------------------------------------------------------------*)
type t = Symbols.channel

let declare table s = fst (declare ~approx:false table s)

let convert table p = fst (Symbols.Channel.convert1 p table)

let pp_channel ppf c =
  (Printer.kws `ProcessChannel) ppf (Symbols.path_to_string c)
    
