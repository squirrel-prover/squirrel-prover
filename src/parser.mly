%token <int> INT
%token <string> ID   /* general purpose identifier */
%token <string> PID  /* predicate identifier */
%token <string> BANG
%token AT PRED
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LANGLE RANGLE
%token AND OR NOT TRUE FALSE HAPPENS
%token EQ NEQ GEQ LEQ COMMA SEMICOLON COLON PLUS MINUS XOR
%token LET IN IF THEN ELSE FIND SUCHTHAT
%token DIFF LEFT RIGHT NONE SEQ EXP
%token NEW OUT PARALLEL NULL
%token CHANNEL TERM PROCESS HASH AENC NAME ABSTRACT MUTABLE SYSTEM
%token INIT INDEX MESSAGE BOOLEAN TIMESTAMP ARROW ASSIGN
%token EXISTS FORALL QUANTIF GOAL EQUIV DARROW AXIOM
%token DOT
%token APPLY TO TRY CYCLE REPEAT NOSIMPL HELP
%token PROOF QED UNDO
%token EOF

%token EMPTY_ELSE

%left XOR
%left EXP

%nonassoc EMPTY_ELSE
%nonassoc ELSE
%nonassoc QUANTIF
%right DARROW
%left OR
%left AND
%nonassoc NOT

%left PLUS
%nonassoc REPEAT
%left SEMICOLON
%nonassoc TRY
%nonassoc NOSIMPL

%start theory
%start top_formula
%start top_process
%start interactive
%type <unit> theory
%type <Theory.formula> top_formula
%type <Process.process> top_process
%type <Prover.parsed_input> interactive

%%

(* Terms *)

timestamp:
| ID term_list                   { Theory.make_term $1 $2 }
| PRED LPAREN timestamp RPAREN   { Theory.Tpred $3 }
| INIT                           { Theory.Tinit }

term:
| LPAREN term RPAREN             { $2 }
| ID term_list                   { Theory.make_term $1 $2 }
| ID term_list AT timestamp      { let ts = $4 in
                                   Theory.make_term ~at_ts:ts $1 $2 }
| LANGLE term COMMA term RANGLE  { Theory.make_pair $2 $4 }
| term XOR term                  { Theory.make_term "xor" [$1;$3] }
| term EXP term                  { Theory.make_term "exp" [$1;$3]}
| INIT                           { Theory.Tinit }
| IF formula THEN term else_term { Theory.ITE ($2,$4,$5) }
| FIND indices SUCHTHAT formula IN term else_term
                                 { Theory.Find ($2,$4,$6,$7) }
| PRED LPAREN term RPAREN        { Theory.Tpred $3 }
| DIFF LPAREN term COMMA term RPAREN { Theory.Diff ($3,$5) }
| LEFT LPAREN term RPAREN        { Theory.Left $3 }
| RIGHT LPAREN term RPAREN       { Theory.Right $3 }
| SEQ LPAREN i=ids ARROW t=term RPAREN { Theory.Seq (i,t) }


term_list:
|                                { [] }
| LPAREN RPAREN                  { [] }
| LPAREN term tm_list RPAREN     { $2::$3 }

tm_list:
|                                { [] }
| COMMA term tm_list             { $2::$3 }

else_term:
| %prec EMPTY_ELSE               { Theory.make_term "zero" [] }
| ELSE term                      { $2 }

(* Facts, aka booleans *)

ord:
| EQ                             { `Eq }
| NEQ                            { `Neq }
| LEQ                            { `Leq }
| LANGLE                         { `Lt }
| GEQ                            { `Geq }
| RANGLE                         { `Gt }

kind:
| INDEX                          { Sorts.eindex }
| MESSAGE                        { Sorts.emessage }
| BOOLEAN                        { Sorts.eboolean }
| TIMESTAMP                      { Sorts.etimestamp }

arg_list:
|                                { [] }
| ids COLON kind                 { List.map (fun x -> x,$3) $1 }
| ids COLON kind COMMA arg_list  { List.map (fun x -> x,$3) $1 @ $5 }

ids:
| ID                             { [$1] }
| ID COMMA ids                   { $1::$3 }

top_formula:
| formula EOF                    { $1 }

formula:
| LPAREN formula RPAREN          { $2 }
| formula AND formula            { Theory.And ($1,$3) }
| formula OR formula             { Theory.Or ($1,$3) }
| formula DARROW formula         { Theory.Impl ($1,$3) }
| NOT formula                    { Theory.Not ($2) }
| FALSE                          { Theory.False }
| TRUE                           { Theory.True }
| term ord term                  { Theory.Compare ($2,$1,$3) }
| PID term_list                  { Theory.make_term $1 $2 }
| PID term_list AT timestamp     { let ts = $4 in
                                   Theory.make_term ~at_ts:ts $1 $2 }
| HAPPENS LPAREN timestamp RPAREN
                                 { Theory.Happens $3 }
| EXISTS LPAREN vs=arg_list RPAREN sep f=formula %prec QUANTIF
                                 { Theory.Exists (vs,f)  }
| FORALL LPAREN vs=arg_list RPAREN sep f=formula %prec QUANTIF
                                 { Theory.ForAll (vs,f)  }
| EXISTS ID COLON kind sep f=formula %prec QUANTIF
                                 { Theory.Exists ([$2,$4],f)  }
| FORALL ID COLON kind sep f=formula %prec QUANTIF
                                 { Theory.ForAll ([$2,$4],f)  }
| DIFF LPAREN f=formula COMMA g=formula RPAREN   { Theory.Diff (f,g) }

sep:
|       {()}
| COMMA {()}

(* Processes *)

top_process:
| process EOF                    { $1 }

process:
| NULL                           { Process.Null }
| LPAREN processes RPAREN        { $2 }
| ID term_list                   { Process.Apply ($1,$2) }
| ID COLON process               { Process.Alias ($3,$1) }
| NEW ID SEMICOLON process       { Process.New ($2,$4) }
| IN LPAREN channel COMMA ID RPAREN process_cont
                                 { Process.In ($3,$5,$7) }
| OUT LPAREN channel COMMA term RPAREN process_cont
                                 { Process.Out ($3,$5,$7) }
| IF f=formula THEN process else_process
                                 { Process.Exists
                                     ([],f,$4,$5) }
| FIND indices SUCHTHAT f=formula IN process else_process
                                 { Process.Exists
                                     ($2,f,$6,$7) }
| LET ID EQ term IN process      { Process.Let ($2,$4,$6) }
| ID term_list ASSIGN term process_cont
                                 { let to_idx = function
                                     | Theory.Var x -> x
                                     | _ -> failwith "index variable expected"
                                   in
                                   let l = List.map to_idx $2 in
                                   Process.Set ($1,l,$4,$5) }
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

opt_arg_list:
| LPAREN arg_list RPAREN         { $2 }
|                                { [] }


name_type:
| MESSAGE                        { 0 }
| INDEX ARROW name_type          { 1+$3 }

msg_or_bool:
| MESSAGE                        { Sorts.emessage }
| BOOLEAN                        { Sorts.eboolean }

state_type:
| msg_or_bool                    { 0, $1 }
| INDEX ARROW state_type         { let n,k = $3 in n+1,k }

abs_type:
| msg_or_bool                    { [],$1 }
| msg_or_bool ARROW abs_type     { let l,r = $3 in $1::l,r }

declaration:
| HASH ID                        { Theory.declare_hash $2 }
| AENC ID                        { Theory.declare_aenc $2 }
| NAME ID COLON name_type        { Theory.declare_name $2 $4 }
| ABSTRACT ID COLON abs_type     { let l,r = $4 in
                                   Theory.declare_abstract $2 l r }
| MUTABLE ID COLON state_type    { Theory.declare_state $2 (fst $4) (snd $4) }
| CHANNEL ID                     { Channel.declare $2 }
| TERM ID opt_arg_list COLON msg_or_bool EQ term
                                 { Theory.declare_macro $2 $3 $5 $7 }
| PROCESS ID opt_arg_list EQ process
                                 { Process.declare $2 $3 $5 }
| AXIOM s=system f=formula       { Prover.add_proved_goal
                                     ("unnamed_goal",
                                      Prover.make_trace_goal s f) }
| AXIOM s=system i=ID COLON f=formula
                                 { Prover.add_proved_goal
                                     (i, Prover.make_trace_goal s f) }

tactic_param:
| t=term    { Prover.Theory t }
| f=formula { Prover.Theory f }

tactic_params:
|                                       { [] }
| t=tactic_param                        { [t] }
| t=tactic_param COMMA ts=tactic_params { t::ts }

tac:
  | LPAREN t=tac RPAREN               { t }
  | l=tac SEMICOLON r=tac             { Tactics.AndThen [l;r] }
  | l=tac PLUS r=tac                  { Tactics.OrElse [l;r] }
  | TRY l=tac                         { Tactics.Try l }
  | REPEAT t=tac                      { Tactics.Repeat t }
  | ID i=INT                          { Tactics.Abstract
                                          ($1,[Prover.Int i]) }
  | ID t=tactic_params                          { Tactics.Abstract
                                                    ($1,t) }
  (* A few special cases for tactics whose names are not parsed as ID
   * because they are reserved. *)
  | LEFT                              { Tactics.Abstract ("left",[]) }
  | RIGHT                             { Tactics.Abstract ("right",[]) }
  | EXISTS t=tactic_params            { Tactics.Abstract
                                          ("exists",t) }
  | NOSIMPL t=tac                     { Tactics.Modifier
                                          ("nosimpl", t) }
  | CYCLE i=INT                       { Tactics.Abstract
                                         ("cycle",[Prover.Int i]) }
  | CYCLE MINUS i=INT                 { Tactics.Abstract
                                         ("cycle",[Prover.Int (-i)]) }

  | APPLY i=ID                        { Tactics.Abstract
                                          ("apply",
                                           [Prover.String_name i]) }
  | APPLY i=ID TO t=tactic_params     { Tactics.Abstract
                                          ("apply",
                                           Prover.String_name i :: t) }
  | HELP                              { Tactics.Abstract
                                          ("help",
                                           []) }

  | HELP i=ID                         { Tactics.Abstract
                                          ("help",
                                           [Prover.String_name i]) }
  (* A few special cases for tactics whose names are not parsed as ID
   * because they are reserved. *)
  | HELP LEFT   { Tactics.Abstract ("help",[Prover.String_name "left"]) }
  | HELP RIGHT  { Tactics.Abstract ("help",[Prover.String_name "right"]) }
  | HELP EXISTS { Tactics.Abstract ("help",[Prover.String_name "exists"]) }

qed:
| QED                                 { () }

undo:
| UNDO i=INT DOT                      { i }

tactic:
| t=tac DOT                           { t }

equiv_item:
| term           { `Message $1 }
| formula        { `Formula $1 }

equiv:
| equiv_item                { [$1] }
| equiv_item COMMA equiv    { $1::$3 }

equiv_env:
|                           { [] }
| LPAREN vs=arg_list RPAREN { vs }

system:
|                         { Action.make_default_system Term.None Action.default_system_name }
| LBRACKET LEFT RBRACKET  { Action.make_default_system Term.Left Action.default_system_name }
| LBRACKET RIGHT RBRACKET { Action.make_default_system Term.Right Action.default_system_name }
| LBRACKET NONE COMMA i=ID RBRACKET  { Action.make_default_system Term.None i }
| LBRACKET LEFT COMMA i=ID RBRACKET  { Action.make_default_system Term.Left i }
| LBRACKET RIGHT COMMA i=ID RBRACKET { Action.make_default_system Term.Right i }

base_system:
| LBRACKET LEFT RBRACKET  { Action.make_base_system Term.Left Action.default_system_name }
| LBRACKET RIGHT RBRACKET { Action.make_base_system Term.Right Action.default_system_name }
| LBRACKET LEFT COMMA i=ID RBRACKET  { Action.make_base_system Term.Left i }
| LBRACKET RIGHT COMMA i=ID RBRACKET  { Action.make_base_system Term.Right i }

goal:
| GOAL s=system i=ID COLON f=formula DOT
                 { Prover.Gm_goal (i, Prover.make_trace_goal s f) }
| GOAL s=system f=formula DOT
                 { Prover.Gm_goal ("unnamed_goal",
                                   Prover.make_trace_goal s f) }
| EQUIV n=ID env=equiv_env COLON l=equiv DOT
                 { Prover.Gm_goal (n, Prover.make_equiv_goal env l) }
| EQUIV n=ID DOT
                 { Prover.Gm_goal
                     (n, Prover.make_equiv_goal_process
			   (Action.make_base_system Term.Left Action.default_system_name)
			   (Action.make_base_system Term.Right Action.default_system_name)) }
| EQUIV b1=base_system b2=base_system n=ID DOT
                 { Prover.Gm_goal
                     (n, Prover.make_equiv_goal_process b1 b2)}

| PROOF          { Prover.Gm_proof }

theory:
| declaration theory             { () }
| SYSTEM process DOT             { Process.declare_system Action.default_system_name $2 }
| SYSTEM LBRACKET i=ID RBRACKET p=process DOT             { Process.declare_system i p }

interactive :
| theory                          { Prover.ParsedInputDescr }
| undo                            { Prover.ParsedUndo $1 }
| tactic                          { Prover.ParsedTactic $1 }
| qed                             { Prover.ParsedQed }
| goal                            { Prover.ParsedGoal $1 }
| EOF                             { Prover.EOF }
