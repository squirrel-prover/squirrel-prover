module Parser = Squirrellib.Parser
module Theory = Squirrellib.Theory
module Lexer = Squirrellib.Lexer

let term_from_string (s:string) = Theory.Local 
    (Parser.top_formula Lexer.token (Lexing.from_string s))

let global_formula_from_string (s:string) = Theory.Global
    (Parser.top_global_formula Lexer.token (Lexing.from_string s))

let sexpr_from_string (s:string) = (Parser.system_expr Lexer.token
                                     (Lexing.from_string s))
