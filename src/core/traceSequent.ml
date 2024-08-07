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
          let empty = SE.empty_system (table s) in
          { system with pair = Some empty; }
        else system
      in
      let es =
        let env = { (S.env s) with system; } in
        ES.init ~env (Equiv.Smart.mk_false)
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
              let id', es = ES.Hyps._add ~force:true id (LDef (se,t)) es in
              assert (Ident.equal id' id);
              es
          ) s es
      in
      es
  end)
