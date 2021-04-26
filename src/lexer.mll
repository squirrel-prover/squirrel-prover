{
  open Lexing
  open Parser
  let newline lexbuf =
    let p = lexbuf.Lexing.lex_curr_p in
    let q =
      { p with Lexing.
        pos_lnum = p.Lexing.pos_lnum+1 ;
        pos_bol = p.Lexing.pos_cnum }
    in
      lexbuf.Lexing.lex_curr_p <- q

  exception Lexical_error of string

  let unterminated_comment () =
    raise (Lexical_error "unterminated comment")


}

let name = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*
let int = ['0'-'9'] ['0'-'9']*

rule token = parse
| [' ' '\t']              { token lexbuf }
| '\n'                    { newline lexbuf ; token lexbuf }
| "(*" { comment lexbuf; token lexbuf }
| "!_" (name as i)  { BANG i }
| "&&"                { AND }
| "||"                { OR }
| "not"               { NOT }
| "True"              { TRUE }
| "False"             { FALSE }
| '<'                 { LANGLE }
| '>'                 { RANGLE }
| '['                 { LBRACKET }
| ']'                 { RBRACKET }
| '?'                 { QMARK }
| ','                 { COMMA }
| "!"                 { BANGU }
| '.'                 { DOT }
| ':'                 { COLON }
| ';'                 { SEMICOLON }
| '*'                 { STAR }
| '_'                 { UNDERSCORE }
| "//"                { SLASHSLASH }
| "/="                { SLASHEQUAL }
| '/'                 { SLASH }
| "@/"                { ATSLASH }
| "="                 { EQ }
| "<>"                { NEQ }
| ">="                { GEQ }
| "<="                { LEQ }
| '('                 { LPAREN }
| ')'                 { RPAREN }
| '|'                 { PARALLEL }
| "->"                { ARROW }
| "=>"                { DARROW }
| "<=>"               { DEQUIVARROW }
| ":="                { ASSIGN }
| "-"                 { MINUS }
| "@"                 { AT }
| "happens"           { HAPPENS }
| "if"                { IF }
| "then"              { THEN }
| "else"              { ELSE }
| "let"               { LET }
| "XOR"               { XOR }
| "by"                { BY }
| "in"                { IN }
| "out"               { OUT }
| "new"               { NEW }
| "try find"          { FIND }
| "such that"         { SUCHTHAT }
| "process"           { PROCESS }
| "abstract"          { ABSTRACT }
| "type"              { TYPE }
| "name_fixed_length" { NAMEFIXEDLENGTH }
| "large"             { LARGE }
| "name"              { NAME }
| "mutable"           { MUTABLE }
| "system"            { SYSTEM }
| "set"               { SET }
| "hash"              { HASH }
| "aenc"              { AENC }
| "senc"              { SENC }
| "signature"         { SIGNATURE }
| "intro"             { INTRO }
| "destruct"          { DESTRUCT }
| "as"                { AS }
| "init"              { INIT }
| "index"             { INDEX }
| "message"           { MESSAGE }
| "channel"           { CHANNEL }
| "boolean"           { BOOLEAN }
| "timestamp"         { TIMESTAMP }
| "null"              { NULL }
| "pred"              { PRED }
| "seq"               { SEQ }
| "oracle"            { ORACLE }
| "with"              { WITH }
| "where"             { WHERE }
| "diff"              { DIFF }
| "left"              { LEFT }
| "^"                 { EXP }
| "right"             { RIGHT }
| "none"              { NONE }
| "forall"            { FORALL }
| "exists"            { EXISTS }
| "goal"              { GOAL }
| "equiv"             { EQUIV }
| "axiom"             { AXIOM }
| "Proof."            { PROOF }
| "Qed."              { QED }
| "Abort."            { ABORT }
| "help"              { HELP }
| "cycle"             { CYCLE }
| "undo"              { UNDO }
| "try"               { TRY }
| "repeat"            { REPEAT }
| "assert"            { ASSERT }
| "exn"               { EXN }
| "use"               { USE }
| "rewrite"           { REWRITE }
| "apply"             { APPLY }
| "revert"            { REVERT }
| "generalize"        { GENERALIZE }
| "depends"           { DEPENDS }
| "clear"             { CLEAR }
| "ddh"               { DDH }
| "nosimpl"           { NOSIMPL }
| "checkfail"         { CHECKFAIL }
| '+'                 { PLUS }
| '\''                { TICK }
| name as n           { ID n }
| int as i            { INT (int_of_string i) }
| eof                 { EOF }

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | "\n"     { new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }
