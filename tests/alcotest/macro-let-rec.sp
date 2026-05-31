inductive opt a =
| None : opt a
| Some : a -> opt a.

let rec proj ['a]  (t :  'a) : opt 'a with 
| _ -> get_proj (Some t)

and get_proj (t:opt 'a) : opt 'a with
 | None -> None
 | Some t -> Some t.
