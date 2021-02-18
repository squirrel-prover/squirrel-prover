open Term

module TraceHyps = TraceSequent.Hyps

module Args = TacticsArgs

module L = Location

(*------------------------------------------------------------------*)
(* Comment in/out for debugging *)
let dbg s = Printer.prt `Ignore s
(* let dbg s = Printer.prt `Dbg s *)

(*------------------------------------------------------------------*)
let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
(** [constraints s] proves the sequent using its trace formulas. *)
let constraints (s : TraceSequent.t) =
  let conclusions =
    Utils.odflt [] (Term.disjunction_to_literals (TraceSequent.conclusion s)) 
  in
  let trace_conclusions =
    List.fold_left (fun acc conc -> match conc with
        | `Pos, (#trace_atom as at) ->
          let at = (at :> Term.generic_atom) in
          Term.(Not (Atom at)) :: acc
        | `Neg, (#trace_atom as at) ->
          Term.Atom at :: acc
        | _ -> acc)
      []
      conclusions
  in
  let s = List.fold_left (fun s f ->
      TraceHyps.add Args.AnyName f s
    ) s trace_conclusions
  in
  TraceSequent.constraints_valid s
