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
        let env = env s in
        S.Hyps.fold (fun id ld es ->
            match ld with
            | LHyp (Global f) -> ES.Hyps.add (Args.Named (Ident.name id)) (LHyp f) es
            | LHyp (Local f) ->
              begin
                match bound s with
                | None ->       (* asymptotic logic *)
                  if HighTerm.is_constant                             env f &&
                     HighTerm.is_single_term_in_se ~se:env.system.set env f
                     (* We can keep an hypothesis ϕ if it is constant
                        and independent of the systems in
                        [env.system.set = l1:P1, ..., ln:Pn]. Indeed, in that case:

                          [ϕ]_{li:Pi} ≡ [ϕ]_{lj:Pj}     for all i,j

                        Thus, writing Γ the local hypotheses (other than ϕ) and ψ the conclusion:
                          [ϕ ⇒ Γ ⇒ ψ]_{l1:P1, ..., ln:Pn}
                          ≡ ⋀ᵢ [ϕ ⇒ Γ ⇒ ψ]_{li:Pi}                 (* by definition *)
                          ≡ ⋀ᵢ [ϕ]_{li:Pi} ⇒ [Γ ⇒ ψ]_{li:Pi}       (* property of [_ ⇒ _] *)
                          ≡ [ϕ]_{l1:P1} ⇒ ⋀ᵢ [Γ ⇒ ψ]_{li:Pi}       (* prop. reasoning  *)
                          ≡ [ϕ]_{l1:P1, ..., ln:Pn} ⇒ ⋀ᵢ [Γ ⇒ ψ]_{l1:P1, ..., ln:Pn}
                     *)
                  then
                    ES.Hyps.add
                      (Args.Named (Ident.name id)) (LHyp (Equiv.mk_reach_atom f)) es
                  else es
                    
                | Some _ -> es
                  (* TODO:Concrete allow to keep the local hypothesis
                     with bound 0 when the bound of the conclusion is
                     more than 0*)
              end
            | LDef (se,t) -> 
              let id', es = ES.Hyps._add ~force:true id (LDef (se,t)) es in
              assert (Ident.equal id' id);
              es
          ) s es
      in
      es
  end)
