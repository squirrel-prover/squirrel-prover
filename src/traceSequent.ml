(** Extends {!LowTraceSequent} with functions relying on the {!Prover} module. *)

module ES = LowEquivSequent
module Args = TacticsArgs

(*------------------------------------------------------------------*) 
include LowTraceSequent

include Sequent.Mk(struct
    module S = LowTraceSequent

    let to_general_sequent s = Goal.Trace s
    let to_global_sequent  s =
      let es =
        ES.init ~env:(S.env s) Equiv.Smart.mk_false
      in
      let es =
        S.Hyps.fold (fun id hyp es ->
            match hyp with
            | Global f -> ES.Hyps.add (Args.Named (Ident.name id)) f es
            | Local f ->
              if HighTerm.is_constant `Exact (env s) f &&
                 HighTerm.is_system_indep (env s) f 
              then
                ES.Hyps.add
                  (Args.Named (Ident.name id)) (Equiv.mk_reach_atom f) es
              else es
          ) s es
      in
      es
  end)
