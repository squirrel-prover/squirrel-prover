let rec tatsts acc = function
  | []                           -> acc
  | `Index _ :: l                -> tatsts acc l
  | `Timestamp (_, ts, ts') :: l -> tatsts (ts :: ts' :: acc) l
  | `Happens ts :: l             -> tatsts (ts :: acc) l

let trace_atoms_ts (at : Term.trace_atom list) =
  tatsts [] at |> List.sort_uniq Stdlib.compare

let rec tatsind acc = function
  | []                           -> acc
  | `Index (_,i,j) :: l          -> tatsind (i :: j :: acc) l
  | `Timestamp (_, ts, ts') :: l -> tatsind acc l
  | `Happens ts :: l             -> tatsind acc l

let trace_atoms_ind (at : Term.trace_atom list) =
  tatsind [] at |> List.sort_uniq Stdlib.compare
