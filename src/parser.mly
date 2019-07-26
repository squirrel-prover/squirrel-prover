%token <string> ID
%token <string> BANG
%token LPAREN RPAREN
%token LANGLE RANGLE
%token AND OR NOT TRUE FALSE
%token EQ COMMA SEMICOLON COLON
%token LET IN IF THEN ELSE FIND SUCHTHAT
%token NEW OUT PARALLEL AS NULL
%token CHANNEL TERM PROCESS HASH AENC NAME MUTABLE SYSTEM
%token INDEX MESSAGE BOOLEAN ARROW ASSIGN
%token EOF

%token EMPTY_ELSE

%nonassoc EMPTY_ELSE
%nonassoc ELSE

%left OR
%left AND
%nonassoc NOT

%start theory
%start top_process
%type <unit> theory
%type <Process.process> top_process
%type <Theory.fact> fact

%%

(* Terms *)

term:
| aterm                          { $1 }
| LANGLE term COMMA term RANGLE  { Theory.make_pair $2 $4 }
| LPAREN term RPAREN             { $2 }

aterm:
| ID term_list                   { Theory.make_term $1 $2 }

term_list:
|                                { [] }
| LPAREN term tm_list RPAREN     { $2::$3 }

tm_list:
|                                { [] }
| COMMA term tm_list             { $2::$3 }

(* Facts, aka booleans *)

ord:
| EQ                             { Term.Eq }

fact:
| LPAREN fact RPAREN             { $2 }
| fact AND fact                  { Term.And  ($1,$3) }
| fact OR fact                   { Term.Or  ($1,$3) }
| NOT fact                       { Term.Not  ($2) }
| FALSE                          { Term.False }
| TRUE                           { Term.True }
| term ord term                  { Term.Atom (Theory.Compare ($2,$1,$3)) }
| ID term_list                   { Term.Atom (Theory.make_term $1 $2) }

(* Processes *)

process:
| NULL                           { Process.Null }
| LPAREN processes RPAREN        { $2 }
| ID term_list                   { Process.Apply ($1,$2,$1) }
| ID term_list AS ID             { Process.Apply ($1,$2,$4) }
| NEW ID SEMICOLON process       { Process.New ($2,$4) }
| IN LPAREN channel COMMA ID RPAREN process_cont
                                 { Process.In ($3,$5,$7) }
| OUT LPAREN channel COMMA term RPAREN process_cont
                                 { Process.Out ($3,$5,$7) }
| IF fact THEN process else_process
                                 { Process.Exists ([],$2,$4,$5) }
| FIND indices SUCHTHAT fact IN process else_process
                                 { Process.Exists ($2,$4,$6,$7) }
| LET ID EQ term IN process      { Process.Let ($2,$4,$6) }
| ID term_list ASSIGN term process_cont
                                 { Process.Set ($1,$2,$4,$5) }
| BANG process                   { Process.Repl ($1,$2) }

processes:
| process                        { $1 }
| process PARALLEL processes     { Process.Parallel ($1,$3) }

process_cont:
|                                { Process.Null }
| SEMICOLON process              { $2 }

else_process:
| %prec EMPTY_ELSE               { Process.Null }
| ELSE process                   { $2 }

channel:
| ID                             { try Channel.of_string $1 with Not_found ->
                                     failwith "unknown channel" }

indices:
| ID                             { [$1] }
| ID COMMA indices               { $1::$3 }

kind:
| INDEX                          { Theory.Index }
| MESSAGE                        { Theory.Message }
| BOOLEAN                        { Theory.Boolean }

arg_list:
|                                { [] }
| ID COLON kind                  { [$1,$3] }
| ID COLON kind COMMA arg_list   { ($1,$3)::$5 }

opt_arg_list:
| LPAREN arg_list RPAREN         { $2 }
|                                { [] }

name_type:
| MESSAGE                        { 0 }
| INDEX ARROW name_type          { 1+$3 }

msg_or_bool:
| MESSAGE                        { Theory.Message }
| BOOLEAN                        { Theory.Boolean }

state_type:
| msg_or_bool                    { 0, $1 }
| INDEX ARROW state_type         { let n,k = $3 in n+1,k }

declaration:
| HASH ID                        { Theory.declare_hash $2 }
| AENC ID                        { Theory.declare_aenc $2 }
| NAME ID COLON name_type        { Theory.declare_name $2 $4 }
| MUTABLE ID COLON state_type    { Theory.declare_state $2 (fst $4) (snd $4) }
| CHANNEL ID                     { Channel.declare $2 }
| TERM ID opt_arg_list COLON msg_or_bool EQ term
                                 { Theory.declare_macro $2 $3 $5 $7 }
| PROCESS ID opt_arg_list EQ process
                                 { Process.declare $2 $3 $5 }

theory:
| declaration theory             { () }
| SYSTEM process EOF             { Process.declare_system Process.Null }

top_process:
| process EOF                    { $1 }
