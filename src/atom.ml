let rec tatsts acc = function
  | [] -> acc
  | (`Index _) :: l -> tatsts acc l
  | (`Timestamp (_, ts, ts')) :: l -> tatsts (ts :: ts' :: acc) l

let trace_atoms_ts at = tatsts [] at |> List.sort_uniq Stdlib.compare

let rec tatsind acc = function
  | [] -> acc
  | (`Index (_,i,j)) :: l -> tatsind (i :: j :: acc) l
  | (`Timestamp (_, ts, ts')) :: l -> tatsind acc l

let trace_atoms_ind at = tatsind [] at |> List.sort_uniq Stdlib.compare
