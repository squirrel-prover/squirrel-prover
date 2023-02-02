module Parser = Squirrellib.Parser
module Theory = Squirrellib.Theory
module Lexer = Squirrellib.Lexer
module Prover = Squirrellib.Prover
module LowTraceSequent = Squirrellib.LowTraceSequent
module LowEquivSequent = Squirrellib.LowEquivSequent

let term_from_string (s:string) = Theory.Local 
    (Parser.top_formula Lexer.token (Lexing.from_string s))

let global_formula_from_string (s:string) = Theory.Global
    (Parser.top_global_formula Lexer.token (Lexing.from_string s))

let sexpr_from_string (s:string) = (Parser.system_expr Lexer.token
                                     (Lexing.from_string s))

let mk_term_from_string s st =
    let env = 
      begin match Prover.get_mode st with
      | ProofMode -> 
        let goal = match Prover.get_current_goal st with
          | None -> assert false
          | Some (ProofObl g)
          | Some (UnprovedLemma (_, g)) -> g
        in
        begin match goal with
          | Trace j -> LowTraceSequent.env j
          | Equiv j -> LowEquivSequent.env j
        end
      | _ -> assert false
      end
    in
    let x = match term_from_string s with 
      | Theory.Local x -> x
      | _ -> assert false
    in
    let cntxt = Theory.{ env; cntxt = InGoal; } in
    let x,_ = Theory.convert cntxt x in x

