(** Extends {!LowTraceSequent} with functions relying on the {!Prover} module. *)

(*------------------------------------------------------------------*) 
module ES = LowEquivSequent
module Args = TacticsArgs
module SE = SystemExpr

(*------------------------------------------------------------------*) 
include LowTraceSequent

include Sequent.Mk(struct
    module S = LowTraceSequent

    let to_general_sequent s = Goal.Local s
        
    let to_global_sequent  s =
      (* The new system of the global sequent. If no system is provided for `pair`,
         use an empty system instead. *)
      let system =
        let system = S.system s in
        if system.pair = None then
          let empty = SE.of_system (table s) (Symbols.System.cast_of_string "Empty") in
          { system with pair = Some (SE.to_pair empty); }
        else system
      in
      let es =
        let env = { (S.env s) with system; } in
        ES.init ~env Equiv.Smart.mk_false
      in
      let es =
        S.Hyps.fold (fun id ld es ->
            match ld with
            | LHyp (Global f) -> ES.Hyps.add (Args.Named (Ident.name id)) (LHyp f) es
            | LHyp (Local f) ->
              if HighTerm.is_constant     (env s) f &&
                 HighTerm.is_system_indep (env s) f 
              then
                ES.Hyps.add
                  (Args.Named (Ident.name id)) (LHyp (Equiv.mk_reach_atom f)) es
              else es
            | LDef (se,t) -> 
              ES.Hyps.add (Args.Named (Ident.name id)) (LDef (se,t)) es
          ) s es
      in
      es
  end)
