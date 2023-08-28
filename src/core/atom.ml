let rec tatsts acc : Term.Lit.xatom list -> Term.term list = function
  | [] -> acc

  | (Comp (_, ts, ts') as at) :: l 
    when Term.Lit.ty_xatom at = Type.Timestamp ->
    tatsts (ts :: ts' :: acc) l

  | Comp (_, _, _) :: l -> tatsts acc l

  | Atom _ :: l -> tatsts acc l
                      
  | Happens ts :: l -> tatsts (ts :: acc) l

let trace_atoms_ts (at : Term.Lit.xatom list) =
  tatsts [] at |> List.sort_uniq Stdlib.compare

let rec tatsind acc : Term.Lit.xatom list -> Vars.vars = function
  | [] -> acc

  | (Comp (_, Term.Var i, Term.Var j) as at) :: l 
    when Term.Lit.ty_xatom at = Type.Index ->
    tatsind (i :: j :: acc) l
      
  | Comp (_, _, _) :: l -> tatsind acc l

  | Happens _ts :: l -> tatsind acc l

  | Atom _ :: l -> tatsind acc l

let trace_atoms_ind (at : Term.Lit.xatom list) =
  tatsind [] at |> List.sort_uniq Stdlib.compare
