let rec tatsts acc : Term.xatom list -> Term.term list = function
  | [] -> acc

  | (`Comp (_, ts, ts') as at) :: l 
    when Term.ty_xatom at = Type.Timestamp ->
    tatsts (ts :: ts' :: acc) l

  | `Comp (_, _, _) :: l -> tatsts acc l

  | `Happens ts :: l -> tatsts (ts :: acc) l

let trace_atoms_ts (at : Term.xatom list) =
  tatsts [] at |> List.sort_uniq Stdlib.compare

let rec tatsind acc : Term.xatom list -> Vars.vars = function
  | [] -> acc

  | (`Comp (_, Term.Var i, Term.Var j) as at) :: l 
    when Term.ty_xatom at = Type.Index ->
    tatsind (i :: j :: acc) l
      
  | `Comp (_, _, _) :: l -> tatsind acc l

  | `Happens _ts :: l -> tatsind acc l

let trace_atoms_ind (at : Term.xatom list) =
  tatsind [] at |> List.sort_uniq Stdlib.compare
