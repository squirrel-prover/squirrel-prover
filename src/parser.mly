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
%token CHANNEL TERM PROCESS HASH AENC SENC SIGNATURE NAME ABSTRACT
%token MUTABLE SYSTEM SET
%token INIT INDEX MESSAGE BOOLEAN TIMESTAMP ARROW ASSIGN
%token EXISTS FORALL QUANTIF GOAL EQUIV DARROW DEQUIVARROW AXIOM
%token DOT
%token WITH ORACLE
%token APPLY TO TRY CYCLE REPEAT NOSIMPL HELP DDH NOBRANCH CHECKFAIL
%token PROOF QED UNDO ABORT
%token EOF
%token EMPTY_ELSE

%nonassoc EMPTY_ELSE

%left XOR
%left EXP

%nonassoc ELSE
%nonassoc QUANTIF
%right DARROW
%right DEQUIVARROW
%left OR
%left AND
%nonassoc NOT

%left PLUS
%nonassoc REPEAT
%left SEMICOLON
%nonassoc TRY
%nonassoc NOSIMPL
%nonassoc NOBRANCH

%start declarations
%start top_formula
%start top_process
%start interactive
%type <Decl.declarations> declarations
%type <Theory.formula> top_formula
%type <Process.process> top_process
%type <Prover.parsed_input> interactive

%%

(* Terms *)

timestamp:
| id=ID terms=term_list             { Theory.App (id, terms) }
| PRED LPAREN ts=timestamp RPAREN   { Theory.Tpred ts }
| INIT                              { Theory.Tinit }

term:
| LPAREN t=term RPAREN                    { t }
| id=ID terms=term_list                   { Theory.App (id, terms) }
| id=ID terms=term_list AT ts=timestamp   { Theory.AppAt (id,terms,ts) }
| LANGLE t=term COMMA t0=term RANGLE      { Theory.App ("pair", [t;t0]) }
| t=term XOR t0=term                      { Theory.App ("xor",  [t;t0]) }
| t=term EXP t0=term                      { Theory.App ("exp",  [t;t0])}
| INIT                                    { Theory.Tinit }
| IF b=formula THEN t=term t0=else_term   { Theory.ITE (b,t,t0) }
| FIND is=indices SUCHTHAT b=formula IN t=term t0=else_term
                                          { Theory.Find (is,b,t,t0) }
| PRED LPAREN t=term RPAREN               { Theory.Tpred t }
| DIFF LPAREN t=term COMMA t0=term RPAREN { Theory.Diff (t,t0) }
| SEQ LPAREN i=ids ARROW t=term RPAREN    { Theory.Seq (i,t) }


term_list:
|                                    { [] }
| LPAREN RPAREN                      { [] }
| LPAREN t=term terms=tm_list RPAREN { t::terms }

tm_list:
|                           { [] }
| COMMA tm=term tms=tm_list { tm::tms }

else_term:
| %prec EMPTY_ELSE               { Theory.App ("zero", []) }
| ELSE t=term                    { t }

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
|                                         { [] }
| is=ids COLON k=kind                     { List.map (fun x -> x,k) is }
| is=ids COLON k=kind COMMA args=arg_list { List.map (fun x -> x,k) is @ args }

ids:
| id=ID                             { [id] }
| id=ID COMMA ids=ids               { id::ids }

top_formula:
| f=formula EOF                    { f }

formula:
| LPAREN f=formula RPAREN                 { f }
| f=formula AND f0=formula                { Theory.And (f,f0) }
| f=formula OR f0=formula                 { Theory.Or (f,f0) }
| f=formula DARROW f0=formula             { Theory.Impl (f,f0) }
| f=formula DEQUIVARROW f0=formula        { Theory.And (Theory.Impl (f,f0), 
                                                        Theory.Impl (f0,f)) }
| NOT f=formula                           { Theory.Not (f) }
| FALSE                                   { Theory.False }
| TRUE                                    { Theory.True }
| f=term o=ord f0=term                    { Theory.Compare (o,f,f0) }
| pid=PID terms=term_list                 { Theory.App (pid, terms) }
| pid=PID terms=term_list AT ts=timestamp { Theory.AppAt (pid, terms, ts) }
| HAPPENS LPAREN ts=timestamp RPAREN      { Theory.Happens ts }
| EXISTS LPAREN vs=arg_list RPAREN sep f=formula %prec QUANTIF
                                 { Theory.Exists (vs,f)  }
| FORALL LPAREN vs=arg_list RPAREN sep f=formula %prec QUANTIF
                                 { Theory.ForAll (vs,f)  }
| EXISTS id=ID COLON k=kind sep f=formula %prec QUANTIF
                                 { Theory.Exists ([id,k],f)  }
| FORALL id=ID COLON k=kind sep f=formula %prec QUANTIF
                                 { Theory.ForAll ([id,k],f)  }
| DIFF LPAREN f=formula COMMA g=formula RPAREN 
                                 { Theory.Diff (f,g) }

sep:
|       {()}
| COMMA {()}

(* Processes *)

top_process:
| p=process EOF                    { p }

process:
| NULL                          { Process.Null }
| LPAREN ps=processes RPAREN    { ps }
| id=ID terms=term_list         { Process.Apply (id,terms) }
| id=ID COLON p=process         { Process.Alias (p,id) }
| NEW id=ID SEMICOLON p=process { Process.New (id,p) }
| IN LPAREN c=ID COMMA id=ID RPAREN p=process_cont
                                { Process.In (c,id,p) }
| OUT LPAREN c=ID COMMA t=term RPAREN p=process_cont
                                { Process.Out (c,t,p) }
| IF f=formula THEN p=process p0=else_process
                                { Process.Exists
                                     ([],f,p,p0) }
| FIND is=indices SUCHTHAT f=formula IN p=process p0=else_process
                                { Process.Exists
                                     (is,f,p,p0) }
| LET id=ID EQ t=term IN p=process
                                { Process.Let (id,t,p) }
| id=ID terms=term_list ASSIGN t=term p=process_cont
                                { let to_idx = function
                                     | Theory.App(x,[]) -> x
                                     | t -> raise @@ Theory.Conv (Index_not_var t)
                                   in
                                   let l = List.map to_idx terms in
                                   Process.Set (id,l,t,p) }
| s=BANG p=process              { Process.Repl (s,p) }

processes:
| p=process                        { p }
| p=process PARALLEL ps=processes  { Process.Parallel (p,ps) }

process_cont:
|                                { Process.Null }
| SEMICOLON p=process            { p }

else_process:
| %prec EMPTY_ELSE               { Process.Null }
| ELSE p=process                 { p }

indices:
| id=ID                          { [id] }
| id=ID COMMA ids=indices        { id::ids }

opt_arg_list:
| LPAREN args=arg_list RPAREN    { args }
|                                { [] }

name_type:
| MESSAGE                        { 0 }
| INDEX ARROW t=name_type        { 1 + t }

msg_or_bool:
| MESSAGE                        { Sorts.emessage }
| BOOLEAN                        { Sorts.eboolean }

state_type:
| t=msg_or_bool                  { 0, t }
| INDEX ARROW t=state_type       { let n,k = t in n+1,k }

msg_type:
| MESSAGE                        { 0 }
| MESSAGE ARROW t=msg_type       { 1 + t }

abs_type:
| t=msg_type                     { 0,t }
| INDEX ARROW t=abs_type         { let i,m = t in i+1,m }

index_arity:
|                                { 0 }
| LPAREN i=INT RPAREN            { i }

declaration:
| HASH e=ID a=index_arity { Decl.Decl_hash (Some a, e, None) }
| HASH e=ID WITH ORACLE f=formula  
                          { Decl.Decl_hash (None, e, Some f) }
| AENC e=ID COMMA d=ID COMMA p=ID
                          { Decl.Decl_aenc (e, d, p) }
| SENC e=ID COMMA d=ID    { Decl.Decl_senc (e, d) }
| SENC e=ID COMMA d=ID WITH h=ID
                          { Decl.Decl_senc_w_join_hash (e, d, h) }
| SIGNATURE s=ID COMMA c=ID COMMA p=ID
                          { Decl.Decl_sign (s, c, p, None) }
| SIGNATURE s=ID COMMA c=ID COMMA p=ID
  WITH ORACLE f=formula   { Decl.Decl_sign (s, c, p, Some f) }
| NAME e=ID COLON t=name_type
                          { Decl.Decl_name (e, t) }
| ABSTRACT e=ID COLON t=abs_type
                          { let index_arity,message_arity = t in
                            Decl.(Decl_abstract
                                    { name = e;
                                      index_arity=index_arity;
                                      message_arity=message_arity;}) }
| MUTABLE e=ID COLON t=state_type
                          { Decl.Decl_state (e, (fst t), (snd t)) }
| CHANNEL e=ID            { Decl.Decl_channel e }
| TERM e=ID args=opt_arg_list COLON typ=msg_or_bool EQ t=term
                          { Decl.Decl_macro (e, args, typ, t) }
| PROCESS e=ID args=opt_arg_list EQ p=process
                          { Decl.Decl_process (e, args, p) }
| AXIOM s=bsystem f=formula
                          { Decl.(Decl_axiom { gname = None;
                                               gsystem = s; 
                                               gform = f; }) }
| AXIOM s=bsystem i=ID COLON f=formula
                          { Decl.(Decl_axiom { gname = Some i;
                                               gsystem = s; 
                                               gform = f; }) }
| SYSTEM p=process 
                          { Decl.(Decl_system { sname = None; 
                                                sprocess = p}) }
| SYSTEM LBRACKET id=ID RBRACKET p=process 
                          { Decl.(Decl_system { sname = Some id; 
                                                sprocess = p}) }

declaration_list:
| decl=declaration                        { [decl] }
| decl=declaration decls=declaration_list { decl :: decls }

declarations:
| decls=declaration_list DOT { decls }

tactic_param:
| t=term    { TacticsArgs.Theory t }
| f=formula { TacticsArgs.Theory f }
| i=INT     { TacticsArgs.Int_parsed i }

tactic_params:
|                                       { [] }
| t=tactic_param                        { [t] }
| t=tactic_param COMMA ts=tactic_params { t::ts }

tac_errors:
|                         { [] }
| i=ID                    { [i] }
| i=ID COMMA t=tac_errors { i::t }

tac:
  | LPAREN t=tac RPAREN                { t }
  | l=tac SEMICOLON r=tac              { Tactics.AndThen [l;r] }
  | l=tac PLUS r=tac                   { Tactics.OrElse [l;r] }
  | TRY l=tac                          { Tactics.Try l }
  | REPEAT t=tac                       { Tactics.Repeat t }
  | id=ID t=tactic_params              { Tactics.Abstract (id,t) }
  (* A few special cases for tactics whose names are not parsed as ID
   * because they are reserved. *)
  | LEFT                               { Tactics.Abstract ("left",[]) }
  | RIGHT                              { Tactics.Abstract ("right",[]) }
  | EXISTS t=tactic_params             { Tactics.Abstract
                                          ("exists",t) }
  | NOSIMPL t=tac                      { Tactics.Modifier
                                          ("nosimpl", t) }
  | NOBRANCH t=tac                     { Tactics.NotBranching (t) }
  | CYCLE i=INT                        { Tactics.Abstract
                                         ("cycle",[TacticsArgs.Int_parsed i]) }
  | CYCLE MINUS i=INT                  { Tactics.Abstract
                                         ("cycle",[TacticsArgs.Int_parsed (-i)]) }
  | CHECKFAIL t=tac WITH ts=tac_errors { Tactics.CheckFail
                                         (Tactics.tac_error_of_strings  ts,t) }

  | APPLY i=ID                         { Tactics.Abstract
                                          ("apply",
                                           [TacticsArgs.String_name i]) }
  | APPLY i=ID TO t=tactic_params      { Tactics.Abstract
                                          ("apply",
                                           TacticsArgs.String_name i :: t) }
  | HELP                               { Tactics.Abstract
                                          ("help",
                                           []) }

  | HELP i=ID                          { Tactics.Abstract
                                          ("help",
                                           [TacticsArgs.String_name i]) }
  | DDH i1=ID COMMA i2=ID COMMA i3=ID  { Tactics.Abstract
                                          ("ddh",
                                           [TacticsArgs.String_name i1;
					                                  TacticsArgs.String_name i2;
					                                  TacticsArgs.String_name i3;
				                                   ]) }
  (* A few special cases for tactics whose names are not parsed as ID
   * because they are reserved. *)
  | HELP LEFT   { Tactics.Abstract ("help",[TacticsArgs.String_name "left"]) }
  | HELP RIGHT  { Tactics.Abstract ("help",[TacticsArgs.String_name "right"]) }
  | HELP EXISTS { Tactics.Abstract ("help",[TacticsArgs.String_name "exists"]) }

qed:
| QED                                 { () }

abort:
| ABORT                               { () }


undo:
| UNDO i=INT DOT                      { i }

tactic:
| t=tac DOT                           { t }

equiv_item:
| t=term           { `Message t }
| f=formula        { `Formula f }

equiv:
| ei=equiv_item                 { [ei] }
| ei=equiv_item COMMA eis=equiv { ei::eis }

equiv_env:
|                           { [] }
| LPAREN vs=arg_list RPAREN { vs }

system:
|                         { Action.(SimplePair default_system_name) }
| LBRACKET LEFT RBRACKET  { Action.(Single (Left default_system_name)) }
| LBRACKET RIGHT RBRACKET { Action.(Single (Right default_system_name)) }
| LBRACKET NONE COMMA i=ID RBRACKET  { Action.(SimplePair i) }
| LBRACKET LEFT COMMA i=ID RBRACKET  { Action.(Single (Left i)) }
| LBRACKET RIGHT COMMA i=ID RBRACKET { Action.(Single (Right i)) }

bsystem:
|                         { Action.(SimplePair default_system_name) }
| LBRACKET i=ID RBRACKET  { Action.(SimplePair i) }

single_system:
| LBRACKET LEFT RBRACKET  { Action.(Left default_system_name)}
| LBRACKET RIGHT RBRACKET { Action.(Right default_system_name)}
| LBRACKET LEFT COMMA i=ID RBRACKET  { Action.(Left i) }
| LBRACKET RIGHT COMMA i=ID RBRACKET { Action.(Right i)}

goal:
| GOAL s=system i=ID COLON f=formula DOT
                 { Prover.Gm_goal (i, Prover.make_trace_goal s f) }
| GOAL s=system f=formula DOT
                 { Prover.Gm_goal (Prover.unnamed_goal (),
                                   Prover.make_trace_goal s f) }
| EQUIV n=ID env=equiv_env COLON l=equiv DOT
                 { Prover.Gm_goal (n, Prover.make_equiv_goal env l) }
| EQUIV n=ID DOT
                 { Prover.Gm_goal
                     (n, Prover.make_equiv_goal_process
                           Action.(Left default_system_name)
			                     Action.(Right default_system_name)) }
| EQUIV b1=single_system b2=single_system n=ID DOT
                 { Prover.Gm_goal
                     (n, Prover.make_equiv_goal_process b1 b2)}

| PROOF          { Prover.Gm_proof }

option_param:
| TRUE  { Config.Param_bool true  }
| FALSE { Config.Param_bool false }
| n=ID  {
        if n = "true" then (Config.Param_bool true)
        else if n = "false" then (Config.Param_bool false)
        else Config.Param_string n   }
| i=INT { Config.Param_int i      }

set_option:
| SET n=ID EQ param=option_param { (n, param) }

interactive :
| set=set_option DOT { Prover.ParsedSetOption set }
| decls=declarations { Prover.ParsedInputDescr decls }
| u=undo             { Prover.ParsedUndo u }
| tac=tactic         { Prover.ParsedTactic tac }
| qed                { Prover.ParsedQed }
| abort              { Prover.ParsedAbort }
| g=goal             { Prover.ParsedGoal g }
| EOF                { Prover.EOF }
