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

  exception LexicalError of string

  let unterminated_comment () =
    raise (LexicalError "unterminated comment")


}

let name = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let int = ['0'-'9'] ['0'-'9']*

rule token = parse
| [' ' '\t']              { token lexbuf }
| '\n'                    { newline lexbuf ; token lexbuf }
| "(*" { comment lexbuf; token lexbuf }
| "!_" (['a'-'z']* as i)  { BANG i }
| "and"               { AND }
| "or"                { OR }
| "not"               { NOT }
| "true"              { TRUE }
| "false"             { FALSE }
| '<'                 { LANGLE }
| '>'                 { RANGLE }
| ','                 { COMMA }
| '.'                 { DOT }
| '_'                 { UNDERSCORE }
| ':'                 { COLON }
| ';'                 { SEMICOLON }
| "="                 { EQ }
| "<>"                { NEQ }
| ">="                { GEQ }
| "<="                { LEQ }
| '('                 { LPAREN }
| ')'                 { RPAREN }
| '['                 { LBRACKET }
| ']'                 { RBRACKET }
| '|'                 { PARALLEL }
| '/'                 { SLASH }
| "->"                { ARROW }
| "=>"                { DARROW }
| ":="                { ASSIGN }
| "-"                 { MINUS }
| "@"                 { AT }
| "if"                { IF }
| "then"              { THEN }
| "else"              { ELSE }
| "let"               { LET }
| "in"                { IN }
| "out"               { OUT }
| "new"               { NEW }
| "try find"          { FIND }
| "such that"         { SUCHTHAT }
| "term"              { TERM }
| "process"           { PROCESS }
| "abstract"          { ABSTRACT }
| "name"              { NAME }
| "mutable"           { MUTABLE }
| "system"            { SYSTEM }
| "hash"              { HASH }
| "aenc"              { AENC }
| "index"             { INDEX }
| "message"           { MESSAGE }
| "channel"           { CHANNEL }
| "boolean"           { BOOLEAN }
| "timestamp"         { TIMESTAMP }
| "as"                { AS }
| "null"              { NULL }
| "forall"            { FORALL }
| "exists"            { EXISTS }
| "goal"              { GOAL }
| "axiom"             { AXIOM }
| "apply"             { APPLY }
| "to"                { TO }
| "Proof."            { PROOF }
| "Qed."              { QED }
| "admit"             { ADMIT }
| "split"             { SPLIT }
| "left"              { LEFT }
| "right"             { RIGHT }
| "intro"             { INTRO }
| "forallintro"       { FORALLINTRO }
| "anyintro"          { ANYINTRO }
| "congruence"        { CONGRUENCE }
| "notraces"          { NOTRACES }
| "eqnames"           { EQNAMES }
| "eqtimestamps"      { EQTIMESTAMPS }
| "euf"               { EUF }
| "cycle"             { CYCLE }
| "undo"              { UNDO }
| "ident"             { IDENT }
| "try"               { TRY }
| "repeat"            { REPEAT }
| "orelse"            { ORELSE }
| '+'                 { PLUS }
| name as n           { ID (n) }
| int as i            { INT (int_of_string i) }
| eof                 { EOF }

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | "\n"     { new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }


