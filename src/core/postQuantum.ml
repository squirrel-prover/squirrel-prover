(* TODO: quantum: update this file *)

open Term
open Utils


(* For the top level occurences of quantum typed messages, we do not
   use Occurences, as it would not create distinct occurences for
   several occurences of the same macro at top-level, which we want
   here.

   We simply recurse inside the term under tuple and collecting
   quantum values, not going under function applications.

   This function enables to verify the syntactic condition 3, see mli. 
*)
let rec get_top_level_quantum table acc t =
  match t with
  | App _
  | Name _
  | Macro _
  | Var _
  | Proj _
    ->
    if (HighType.is_classical table (Term.ty t)) then
      acc
    else  t::acc
  | Let (_,_,t) | Quant (_,_,t) -> get_top_level_quantum table acc t
  | Tuple ts -> List.fold_left (get_top_level_quantum table) acc ts
  | Diff pts ->
    (* FEATURE: Here, we consider the Diff as a tuple, which limits
       the possibilities. Could be generalized to allow for diff over
       quantum values. *)
    begin
      match pts with
        Explicit epts ->
        List.fold_left (fun acc (_, pt) ->
            get_top_level_quantum table acc pt) acc epts
    end
  | Find (_,t1,t2,t3) -> List.fold_left (get_top_level_quantum table) acc [t1;t2;t3] 
  | _ -> acc


(* see mli *)
let check_direct_quantum_value_occurences
    (context : ProofContext.t)
    (ts:terms)
  =
  let table  = context.env.table  in

  (* Otherwise, we then check top level occurences of quantum values. *) 
  let occs2 =
    List.fold_left (get_top_level_quantum table) [] ts
  in

  List.length occs2 <= 1 
