%{
  module L  = Location
  module T  = Tactics

  let sloc startpos endpos s =
    let loc = L.make startpos endpos in
    L.mk_loc loc s

  let mk_abstract loc s args = T.Abstract (L.mk_loc loc s, args) 
%}

%token <int> INT
%token <string> ID   /* general purpose identifier */
%token <string> INFIXSYMB   /* infix function symbols */
%token <string> BANG
%token AT PRED
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LANGLE RANGLE
%token GAND GOR AND OR NOT TRUE FALSE HAPPENS
%token EQ NEQ GEQ LEQ COMMA SEMICOLON COLON PLUS MINUS COLONEQ
%token XOR STAR UNDERSCORE QMARK TICK 
%token LET IN IF THEN ELSE FIND SUCHTHAT
%token TILDE DIFF LEFT RIGHT SEQ
%token NEW OUT PARALLEL NULL
%token CHANNEL PROCESS HASH AENC SENC SIGNATURE NAME ABSTRACT TYPE FUN
%token MUTABLE SYSTEM SET
%token INIT INDEX MESSAGE BOOLEAN TIMESTAMP ARROW RARROW 
%token EXISTS FORALL QUANTIF GOAL EQUIV DARROW DEQUIVARROW AXIOM
%token LOCAL GLOBAL
%token DOT SLASH BANGU SLASHEQUAL SLASHSLASH SLASHSLASHEQUAL ATSLASH
%token TIME WHERE WITH ORACLE EXN
%token LARGE NAMEFIXEDLENGTH
%token TRY CYCLE REPEAT NOSIMPL HELP DDH CHECKFAIL ASSERT USE 
%token REWRITE REVERT CLEAR GENERALIZE DEPENDENT DEPENDS APPLY 
%token SPLITSEQ CONSTSEQ MEMSEQ
%token BY INTRO AS DESTRUCT REMEMBER INDUCTION
%token PROOF QED UNDO ABORT HINT
%token INCLUDE
%token EOF

%nonassoc QUANTIF
%right ARROW
%right DARROW
%right DEQUIVARROW
%left AND OR
%left GAND GOR

%nonassoc TRUE SEQ PRED NOT LPAREN INIT ID UNDERSCORE HAPPENS FALSE DIFF

%nonassoc EQ NEQ GEQ LEQ LANGLE RANGLE

%nonassoc empty_else
%nonassoc ELSE

%left INFIXSYMB 

%left XOR

%nonassoc AT

%nonassoc tac_prec

%left PLUS
%right SEMICOLON
%nonassoc BY
%nonassoc REPEAT
%nonassoc TRY
%nonassoc NOSIMPL

%start declarations
%start top_formula
%start top_process
%start interactive
%type <Decl.declarations> declarations
%type <Theory.formula> top_formula
%type <Process.process> top_process
%type <Prover.parsed_input> interactive

%%

(* Locations *)
%inline loc(X):
| x=X {
    { L.pl_desc = x;
      L.pl_loc  = L.make $startpos $endpos;
    }
  }

%inline lloc(X):
| X { L.make $startpos $endpos }

(* Lists *)
%inline empty:
| { () }

%inline slist(X, S):
| l=separated_list(S, X) { l }

%inline slist1(X, S):
| l=separated_nonempty_list(S, X) { l }

(* Terms *)
lsymb:
| id=loc(ID) { id }

/* non-ambiguous term */
sterm_i:
| LPAREN t=term_i RPAREN        { t }
| id=lsymb                      { Theory.App (id, []) }
| UNDERSCORE                    { Theory.Tpat }

| LANGLE t=term COMMA t0=term RANGLE
    { let fsymb = sloc $startpos $endpos "pair" in
      Theory.App (fsymb, [t;t0]) }

/* formula */

| DIFF LPAREN t=term COMMA t0=term RPAREN { Theory.Diff (t,t0) }

| SEQ LPAREN vs=arg_list ARROW t=term RPAREN    { Theory.Seq (vs,t) }

| l=loc(NOT) f=sterm 
    { let fsymb = L.mk_loc (L.loc l) "not" in
      Theory.App (fsymb,[f]) }

| l=lloc(FALSE)  { Theory.App (L.mk_loc l "false",[]) }

| l=lloc(TRUE)   { Theory.App (L.mk_loc l "true",[]) }

| HAPPENS LPAREN ts=slist1(term,COMMA) RPAREN
                                          { Theory.Happens ts }

/* timestamp */

| PRED LPAREN ts=term RPAREN             { Theory.Tpred ts }
| INIT                                   { Theory.Tinit }

%inline infix_s:
| AND         { "&&"  }
| OR          { "||"   }
| s=INFIXSYMB { s }
| XOR         { "xor"  }
| DARROW      { "=>" }

/* ambiguous term */
term_i:
| f=sterm_i                                  { f }
| id=lsymb terms=term_list1                  { Theory.App (id, terms) }
| id=lsymb AT ts=term                        { Theory.AppAt (id,[],ts) }
| id=lsymb terms=term_list1 AT ts=term       { Theory.AppAt (id,terms,ts) }

| t=term s=loc(infix_s) t0=term             { Theory.App (s, [t;t0]) }

| f=term l=lloc(DEQUIVARROW) f0=term
    { let loc = L.make $startpos $endpos in
      let fi = L.mk_loc l "=>" in
      let fa = L.mk_loc l "&&"  in
      Theory.App (fa, [L.mk_loc loc (Theory.App (fi, [f;f0]));
                       L.mk_loc loc (Theory.App (fi, [f0;f]))]) }
 
| IF b=term THEN t=term t0=else_term
    { let fsymb = sloc $startpos $endpos "if" in
      Theory.App (fsymb,  [b;t;t0]) }

| FIND is=indices SUCHTHAT b=term IN t=term t0=else_term
                                          { Theory.Find (is,b,t,t0) }

| f=term o=ord f0=term                    { Theory.Compare (o,f,f0) }

| EXISTS LPAREN vs=arg_list RPAREN sep f=term %prec QUANTIF
                                 { Theory.Exists (vs,f)  }

| FORALL LPAREN vs=arg_list RPAREN sep f=term %prec QUANTIF
                                 { Theory.ForAll (vs,f)  }

| EXISTS a=arg sep f=term %prec QUANTIF
                                 { Theory.Exists (a,f)  }

| FORALL a=arg sep f=term %prec QUANTIF
                                 { Theory.ForAll (a,f)  }

/* non-ambiguous term */
%inline else_term:
| %prec empty_else   { let loc = L.make $startpos $endpos in
                       let fsymb = L.mk_loc loc "zero" in
                       L.mk_loc loc (Theory.App (fsymb, [])) }
| ELSE t=term       { t }

sterm:
| t=loc(sterm_i) { t }

term:
| t=loc(term_i) { t }

term_list:
|                                    { [] }
| LPAREN RPAREN                      { [] }
| LPAREN t=term terms=tm_list RPAREN { t::terms }

term_list1:
| LPAREN t=term terms=tm_list RPAREN { t::terms }

tm_list:
|                           { [] }
| COMMA tm=term tms=tm_list { tm::tms }

(* Facts, aka booleans *)

%inline ord:
| EQ                             { `Eq }
| NEQ                            { `Neq }
| LEQ                            { `Leq }
| LANGLE                         { `Lt }
| GEQ                            { `Geq }
| RANGLE                         { `Gt }

arg:
| is=ids COLON k=p_ty                     { List.map (fun x -> x,k) is }

arg_list:
|                                         { [] }
| is=ids COLON k=p_ty                     { List.map (fun x -> x,k) is }
| is=ids COLON k=p_ty COMMA args=arg_list { List.map (fun x -> x,k) is @ args }

ids:
| id=lsymb                             { [id] }
| id=lsymb COMMA ids=ids               { id::ids }

top_formula:
| f=term EOF                    { f }

sep:
|       {()}
| COMMA {()}

(* higher-order terms *)

hterm_i:
| FUN LPAREN args=arg_list RPAREN ARROW t=term { Theory.Lambda (args,t) }

hterm:
| t=loc(hterm_i) { t }

(* Processes *)

top_process:
| p=process EOF                    { p }

colon_ty:
| COLON t=p_ty { t }

process_i:
| NULL                             { Process.Null }
| LPAREN ps=processes_i RPAREN     { ps }
| id=lsymb terms=term_list         { Process.Apply (id,terms) }
| id=lsymb COLON p=process         { Process.Alias (p,id) }

| NEW id=lsymb ty=colon_ty? SEMICOLON p=process
    { let ty = match ty with
        | Some ty -> ty
        | None -> L.mk_loc (L.loc id) Theory.P_message 
      in
      Process.New (id,ty,p) }

| IN LPAREN c=lsymb COMMA id=lsymb RPAREN p=process_cont
    { Process.In (c,id,p) }

| OUT LPAREN c=lsymb COMMA t=term RPAREN p=process_cont
    { Process.Out (c,t,p) }

| IF f=term THEN p=process p0=else_process
    { Process.Exists ([],f,p,p0) }

| FIND is=indices SUCHTHAT f=term IN p=process p0=else_process
    { Process.Exists (is,f,p,p0) }

| LET id=lsymb ty=colon_ty? EQ t=term IN p=process
    { Process.Let (id,t,ty,p) }

| id=lsymb terms=term_list COLONEQ t=term p=process_cont
    { let to_idx t = match L.unloc t with
        | Theory.App(x,[]) -> x
        | ti -> raise @@ Theory.Conv (L.loc t, Theory.Index_not_var ti)
      in
      let l = List.map to_idx terms in
      Process.Set (id,l,t,p) }

| s=loc(BANG) p=process { Process.Repl (s,p) }

process:
| p=loc(process_i) { p }

processes_i:
| p=process_i                             { p }
| p=process PARALLEL ps=loc(processes_i)  { Process.Parallel (p,ps) }

process_cont:
|                                { let loc = L.make $startpos $endpos in
                                   L.mk_loc loc Process.Null }
| SEMICOLON p=process            { p }

else_process:
| %prec empty_else               { let loc = L.make $startpos $endpos in
                                   L.mk_loc loc Process.Null }
| ELSE p=process                 { p }

indices:
| id=lsymb                          { [id] }
| id=lsymb COMMA ids=indices        { id::ids }

opt_arg_list:
| LPAREN args=arg_list RPAREN    { args }
|                                { [] }

name_type:
| ty=p_ty                     { 0,ty }
| INDEX ARROW t=name_type     { let i,ty = t in
                                1 + i,ty }

ty_var:
| TICK id=lsymb     { id }

index_arity:
|                                { 0 }
| LPAREN i=INT RPAREN            { i }

p_ty_i:
| MESSAGE      { Theory.P_message }
| INDEX        { Theory.P_index }
| TIMESTAMP    { Theory.P_timestamp }
| BOOLEAN      { Theory.P_boolean }
| tv=ty_var    { Theory.P_tvar tv }
| l=lsymb      { Theory.P_tbase l }

p_ty:
| ty=loc(p_ty_i) { ty }

fun_ty:
| l=slist1(p_ty,ARROW)      { l }

/* crypto assumption typed space */
c_ty:
| l=lsymb COLON ty=p_ty { Decl.{ cty_space = l; 
                                 cty_ty    = ty; } }

/* crypto assumption typed space */
c_tys:
| WHERE list=slist1(c_ty, empty) { list }
|                                { [] }

ty_args:
|                                          { [] }
| LBRACKET ids=slist1(ty_var,empty) RBRACKET { ids }

bty_info:
| NAMEFIXEDLENGTH { Symbols.Ty_name_fixed_length }
| LARGE           { Symbols.Ty_large }

bty_infos:
| LBRACKET l=slist(bty_info,COMMA) RBRACKET { l }
|                                           { [] }

lsymb_decl:
| id=lsymb                       { `Prefix, id }
| LPAREN s=loc(INFIXSYMB) RPAREN { `Infix, s }

declaration_i:
| HASH e=lsymb a=index_arity ctys=c_tys
                          { Decl.Decl_hash (Some a, e, None, ctys) }

| HASH e=lsymb WITH ORACLE f=term
                          { Decl.Decl_hash (None, e, Some f, []) }

| AENC e=lsymb COMMA d=lsymb COMMA p=lsymb ctys=c_tys
                          { Decl.Decl_aenc (e, d, p, ctys) }

| SENC e=lsymb COMMA d=lsymb ctys=c_tys
                          { Decl.Decl_senc (e, d, ctys) }

| SENC e=lsymb COMMA d=lsymb WITH HASH h=lsymb
                          { Decl.Decl_senc_w_join_hash (e, d, h) }

| SIGNATURE s=lsymb COMMA c=lsymb COMMA p=lsymb ctys=c_tys
                          { Decl.Decl_sign (s, c, p, None, ctys) }

| SIGNATURE s=lsymb COMMA c=lsymb COMMA p=lsymb
  WITH ORACLE f=term       
                          { Decl.Decl_sign (s, c, p, Some f, []) }

| DDH g=lsymb COMMA ei=lsymb_decl ctys=c_tys
    { let e, f_info = ei in
      Decl.Decl_ddh (g,(f_info,e), ctys) }

| NAME e=lsymb COLON t=name_type
                          { let a,ty = t in 
                            Decl.Decl_name (e, a, ty) }

| TYPE e=lsymb infos=bty_infos 
                          { Decl.Decl_bty { bty_name = e; bty_infos = infos; } }

| ABSTRACT e=lsymb_decl a=ty_args COLON t=fun_ty
    { let symb_type, name = e in
      Decl.(Decl_abstract
              { name      = name;
                symb_type = symb_type;
                ty_args   = a;
                abs_tys   = t; }) }

| MUTABLE e=lsymb args=opt_arg_list COLON typ=p_ty EQ t=term
                          { Decl.Decl_state (e, args, typ, t) }

| CHANNEL e=lsymb         { Decl.Decl_channel e }

| PROCESS e=lsymb args=opt_arg_list EQ p=process
                          { Decl.Decl_process (e, args, p) }

|        AXIOM s=local_statement  { Decl.Decl_axiom s }
|  LOCAL AXIOM s=local_statement  { Decl.Decl_axiom s }
| GLOBAL AXIOM s=global_statement { Decl.Decl_axiom s }

| SYSTEM p=process
                          { Decl.(Decl_system { sname = None;
                                                sprocess = p}) }

| SYSTEM LBRACKET id=lsymb RBRACKET p=process
                          { Decl.(Decl_system { sname = Some id;
                                                sprocess = p}) }

declaration:
| ldecl=loc(declaration_i)                  { ldecl }

declaration_list:
| decl=declaration                        { [decl] }
| decl=declaration decls=declaration_list { decl :: decls }

declarations:
| decls=declaration_list DOT { decls }

tactic_param:
| f=term %prec tac_prec  { TacticsArgs.Theory f }
| i=loc(INT)             { TacticsArgs.Int_parsed i }

tactic_params:
|                                       { [] }
| t=tactic_param                        { [t] }
| t=tactic_param COMMA ts=tactic_params { t::ts }

(*------------------------------------------------------------------*)
rw_mult:
| BANGU  { `Many }
| QMARK  { `Any }
|        { `Once }

rw_dir:
|       { `LeftToRight }
| MINUS { `RightToLeft }

rw_type:
| pt=spt             { `Rw pt }  
| SLASH t=sterm      { `Expand t }
| SLASH l=lloc(STAR)  { `ExpandAll l }

expnd_type:
| ATSLASH t=sterm      { `Expand t }
| ATSLASH l=lloc(STAR)  { `ExpandAll l }

rw_item:
| m=rw_mult d=loc(rw_dir) t=rw_type  { TacticsArgs.{ rw_mult = m; 
                                                     rw_dir = d; 
                                                     rw_type = t; } }

rw_equiv_item:
| d=loc(rw_dir) pt=pt  { TacticsArgs.{ rw_mult = `Once; 
                                       rw_dir = d; 
                                       rw_type = `Rw pt; } }

expnd_item:
| d=loc(rw_dir) t=expnd_type  { TacticsArgs.{ rw_mult = `Once; 
                                              rw_dir = d; 
                                              rw_type = t; } }


rw_arg:
| r=rw_item { TacticsArgs.R_item r }
| s=s_item  { TacticsArgs.R_s_item s }

rw_args:
| l=slist1(rw_arg, empty) { l }

single_target:
| id=lsymb { id }
| i=loc(int)    { L.mk_loc (L.loc i) (string_of_int (L.unloc i)) }

in_target:
|                                  { `Goal }
| IN l=slist1(single_target,COMMA) { `Hyps l }
| IN STAR                          { `All }

apply_in:
|             { None }
| IN id=lsymb { Some id }

(*------------------------------------------------------------------*)
naming_pat:
| UNDERSCORE  { TacticsArgs.Unnamed }
| QMARK       { TacticsArgs.AnyName }
| id=ID       { TacticsArgs.Named id }

and_or_pat:
| LBRACKET s=simpl_pat          ips=slist(simpl_pat, empty)    RBRACKET
                    { TacticsArgs.And (s :: ips) }
| LBRACKET s=simpl_pat PARALLEL ips=slist(simpl_pat, PARALLEL) RBRACKET
                    { TacticsArgs.Or  (s :: ips) }
| LBRACKET RBRACKET { TacticsArgs.Split }

ip_rw_dir:
| ARROW  { `LeftToRight }
| RARROW { `RightToLeft }

simpl_pat:
| n_ip=naming_pat  { TacticsArgs.SNamed n_ip }
| ao_ip=and_or_pat { TacticsArgs.SAndOr ao_ip }
| d=loc(ip_rw_dir) { TacticsArgs.Srewrite d }

s_item:
| l=loc(SLASHSLASH)      { TacticsArgs.Tryauto      (L.loc l)}
| l=loc(SLASHEQUAL)      { TacticsArgs.Simplify     (L.loc l)}
| l=loc(SLASHSLASHEQUAL) { TacticsArgs.Tryautosimpl (L.loc l)}

intro_pat:
| s=s_item      { TacticsArgs.SItem (s) }
| l=loc(STAR)   { TacticsArgs.Star  (L.loc l)}
| l=loc(RANGLE) { TacticsArgs.StarV (L.loc l)}
| pat=simpl_pat { TacticsArgs.Simpl pat }
| e=expnd_item  { TacticsArgs.SExpnd e }

intro_pat_list:
| l=slist1(intro_pat,empty) { l }

(*------------------------------------------------------------------*)
int:
|i=INT { i }

selector:
| l=slist1(int,COMMA) { l }

tac_term:
| f=term  %prec tac_prec { f }

as_ip:
| AS ip=simpl_pat { ip }

as_n_ips:
| AS n_ips=slist1(naming_pat, empty) { n_ips }

%inline sel_tac:
| s=selector COLON r=tac { (s,r) }

sel_tacs:
| l=slist1(sel_tac,PARALLEL) { l }

pt:
| hid=lsymb args=slist(sterm,empty)
    { let p_pt_loc = L.make $startpos $endpos in
      { p_pt_hid = hid; p_pt_args = args; p_pt_loc; } }

/* legacy syntax for use tactic */
pt_use_tac:
| hid=lsymb
    { Theory.{ p_pt_hid = hid; p_pt_args = []; p_pt_loc = L.loc hid; } }
| hid=lsymb WITH args=slist1(tac_term,COMMA) 
    { let p_pt_loc = L.make $startpos $endpos in
      Theory.{ p_pt_hid = hid; p_pt_args = args; p_pt_loc; } }

/* non-ambiguous pt */
spt:
| hid=lsymb
    { Theory.{ p_pt_hid = hid; p_pt_args = []; p_pt_loc = L.loc hid; } }
| LPAREN pt=pt RPAREN
    { pt }

apply_arg:
| pt=pt                  { Theory.PT_hol pt }

constseq_arg:
| LPAREN b=hterm RPAREN t=sterm { (b,t) }

(*------------------------------------------------------------------*)
%inline generalize_dependent:
| GENERALIZE DEPENDENT { }

%inline dependent_induction:
| DEPENDENT INDUCTION { }

%inline rewrite_equiv:
| REWRITE EQUIV { }

%inline assert_tac:
| l=lloc(ASSERT) p=tac_term ip=as_ip?
    { let ip = match ip with
        | None -> []
        | Some ip -> [TacticsArgs.SimplPat ip] in
      mk_abstract l "assert" (TacticsArgs.Theory p :: ip) }

(*------------------------------------------------------------------*)
/* tactics named arguments */

named_arg:
| TILDE l=lsymb { TacticsArgs.NArg l }

named_args:
| args=slist(named_arg, empty) { args }

(*------------------------------------------------------------------*)
tac:
  | LPAREN t=tac RPAREN                { t }
  | l=tac SEMICOLON r=tac              { T.AndThen [l;r] }
  | l=tac SEMICOLON LBRACKET sls=sel_tacs RBRACKET
                                       { T.AndThenSel (l,sls) }
  | l=tac SEMICOLON sl=sel_tac %prec tac_prec
                                       { T.AndThenSel (l,[sl]) }
  | l=lloc(BY) t=tac %prec tac_prec    { T.By (t,l) }
  | l=tac PLUS r=tac                   { T.OrElse [l;r] }
  | TRY l=tac                          { T.Try l }
  | REPEAT t=tac                       { T.Repeat t }
  | id=lsymb t=tactic_params           { mk_abstract (L.loc id) (L.unloc id) t }

  (* Special cases for tactics whose names are not parsed as ID
   * because they are reserved. *)

  | l=lloc(LEFT)                       { mk_abstract l "left"  [] }
  | l=lloc(RIGHT)                      { mk_abstract l "right" [] }

  | l=lloc(INTRO) p=intro_pat_list
    { mk_abstract l "intro" [TacticsArgs.IntroPat p] }

  | t=tac l=lloc(DARROW) p=intro_pat_list
    { T.AndThen [t; mk_abstract l "intro" [TacticsArgs.IntroPat p]] }

  | l=lloc(DESTRUCT) i=lsymb
    { mk_abstract l "destruct" [TacticsArgs.String_name i] }

  | l=lloc(DESTRUCT) i=lsymb AS p=and_or_pat   
    { mk_abstract l "destruct" [TacticsArgs.String_name i; 
                                TacticsArgs.AndOrPat p] }

  | l=lloc(DEPENDS) args=tactic_params
    { mk_abstract l "depends" args }

  | l=lloc(DEPENDS) args=tactic_params l1=lloc(BY) t=tac
    { T.AndThenSel (mk_abstract l "depends" args, [[1], T.By (t,l1)]) }

  | l=lloc(REMEMBER) t=term AS id=lsymb
    { mk_abstract l "remember" [TacticsArgs.Remember (t, id)] }

  | l=lloc(EXISTS) t=tactic_params
    { mk_abstract l "exists" t }

  | NOSIMPL t=tac                      { T.Modifier ("nosimpl", t) }
  | TIME t=tac  %prec tac_prec         { T.Time t }

  | l=lloc(CYCLE) i=loc(INT)
    { mk_abstract l "cycle" [TacticsArgs.Int_parsed i] }

  | l=lloc(CYCLE) MINUS i=loc(INT)
    { let im = L.mk_loc (L.loc i) (- (L.unloc i)) in
      mk_abstract l "cycle" [TacticsArgs.Int_parsed im] }

  | CHECKFAIL t=tac EXN ts=ID  { T.CheckFail (ts, t) }

  | l=lloc(REVERT) ids=slist1(lsymb, empty)     
    { let ids = List.map (fun id -> TacticsArgs.String_name id) ids in
      mk_abstract l "revert" ids }

  | l=lloc(GENERALIZE) terms=slist1(sterm, empty) n_ips_o=as_n_ips?
    { mk_abstract l "generalize" [TacticsArgs.Generalize (terms, n_ips_o)] }

  | l=lloc(generalize_dependent) terms=slist1(sterm, empty) n_ips_o=as_n_ips?
    { mk_abstract l "generalize dependent"
                  [TacticsArgs.Generalize (terms, n_ips_o)] }

  | l=lloc(INDUCTION) t=tactic_params
    { mk_abstract l "induction" t}

  | l=lloc(dependent_induction) t=tactic_params
    { mk_abstract l "dependent induction" t }

  | l=lloc(CLEAR) ids=slist1(lsymb, empty)     
    { let ids = List.map (fun id -> TacticsArgs.String_name id) ids in
      mk_abstract l "clear" ids }

  | t=assert_tac { t }

  | t=assert_tac l=lloc(BY) t1=tac
    { T.AndThenSel (t, [[1], T.By (t1,l)]) }

  | l=lloc(USE) pt=pt_use_tac ip=as_ip? 
    { mk_abstract l "assert" [TacticsArgs.AssertPt (pt, ip, `IntroImpl)] }

  | l=lloc(ASSERT) LPAREN ip=simpl_pat? COLONEQ pt=pt RPAREN
    { mk_abstract l "assert" [TacticsArgs.AssertPt (pt, ip, `None)] }

  | l=lloc(REWRITE) p=rw_args w=in_target
    { mk_abstract l "rewrite" [TacticsArgs.RewriteIn (p, w)] }

  | l=lloc(rewrite_equiv) p=rw_equiv_item
    { mk_abstract l "rewrite equiv" [TacticsArgs.RewriteEquiv (p)] }

  | l=lloc(APPLY) a=named_args t=apply_arg w=apply_in
    { mk_abstract l "apply" [TacticsArgs.ApplyIn (a, t, w)] }

  | l=lloc(SPLITSEQ) i=loc(INT) COLON LPAREN ht=hterm RPAREN 
    { mk_abstract l "splitseq" [TacticsArgs.SplitSeq (i, ht)] }

  | l=lloc(CONSTSEQ) i=loc(INT) COLON terms=slist1(constseq_arg, empty)
    { mk_abstract l "constseq" [TacticsArgs.ConstSeq (i, terms)] }

  | l=lloc(MEMSEQ) i=loc(INT) j=loc(INT)
    { mk_abstract l "memseq" [TacticsArgs.MemSeq (i, j)] }

  | l=lloc(DDH) g=lsymb COMMA i1=lsymb COMMA i2=lsymb COMMA i3=lsymb 
    { mk_abstract l "ddh"
         [TacticsArgs.String_name g;
          TacticsArgs.String_name i1;
					TacticsArgs.String_name i2;
					TacticsArgs.String_name i3] }

  | l=lloc(HELP)
    { mk_abstract l "help" [] }

  | l=lloc(HELP) i=lsymb
    { mk_abstract l "help" [TacticsArgs.String_name i] }

  | l=lloc(HELP) h=help_tac
   { mk_abstract l "help" [TacticsArgs.String_name h] }

(* A few special cases for tactics whose names are not parsed as ID
 * because they are reserved. *)
help_tac_i:
| LEFT       { "left"}     
| RIGHT      { "right"}    
| INTRO      { "intro"} 
| DESTRUCT   { "destruct"} 
| DEPENDS    { "depends"}
| REMEMBER   { "remember"}
| EXISTS     { "exists"}    
| REVERT     { "revert"}  
| GENERALIZE { "generalize"}  
| INDUCTION  { "induction"}  
| CLEAR      { "clear"}      
| ASSERT     { "assert"}   
| USE        { "use"}      
| REWRITE    { "rewrite"}  
| APPLY      { "apply"}  
| SPLITSEQ   { "splitseq"}  
| CONSTSEQ   { "constseq"}  
| MEMSEQ     { "memseq"}  
| DDH        { "ddh"}      

| DEPENDENT INDUCTION  { "dependent induction"}  
| GENERALIZE DEPENDENT { "generalize dependent"}  
| REWRITE EQUIV        { "rewrite equiv"}  

help_tac:
| l=loc(help_tac_i) { l }

undo:
| UNDO i=INT DOT                      { i }

tactic:
| t=tac DOT                           { t }

biframe:
| ei=term                   { [ei] }
| ei=term COMMA eis=biframe { ei::eis }

%inline quant:
| FORALL { Theory.PForAll }
| EXISTS { Theory.PExists }
      
global_formula_i:
| LBRACKET f=term RBRACKET         { Theory.PReach f }
| TILDE LPAREN e=biframe RPAREN    { Theory.PEquiv e }
| EQUIV LPAREN e=biframe RPAREN    { Theory.PEquiv e }
| LPAREN f=global_formula_i RPAREN { f }

| f=global_formula ARROW f0=global_formula { Theory.PImpl (f,f0) }

| q=quant LPAREN vs=arg_list RPAREN sep f=global_formula %prec QUANTIF
                                   { Theory.PQuant (q,vs,f)  }

| f1=global_formula GAND f2=global_formula 
                                   { Theory.PAnd (f1, f2) }
| f1=global_formula GOR f2=global_formula 
                                   { Theory.POr (f1, f2) }

global_formula:
| f=loc(global_formula_i) { f }


/* -----------------------------------------------------------------------
 * Systems
 * ----------------------------------------------------------------------- */

system_proj:
| LEFT                { SystemExpr.(P_Left  default_system_name) }
| RIGHT               { SystemExpr.(P_Right default_system_name) }
| i=lsymb SLASH LEFT  { SystemExpr. P_Left                    i  }
| i=lsymb SLASH RIGHT { SystemExpr. P_Right                   i  }

/* A single or bi-system */
system:
|                                  { SystemExpr.P_SimplePair
                                       SystemExpr.default_system_name }
| LBRACKET i=lsymb        RBRACKET { SystemExpr. P_SimplePair i }
| LBRACKET sp=system_proj RBRACKET { SystemExpr. P_Single sp }

/* A bi-system */
bisystem:
|                                  { SystemExpr.(P_SimplePair default_system_name) }
| LBRACKET i=lsymb RBRACKET        { SystemExpr. P_SimplePair i }
| LBRACKET s1=system_proj COMMA s2=system_proj RBRACKET
                                   { SystemExpr. P_Pair (s1, s2) }


/* -----------------------------------------------------------------------
 * Statements and goals
 * ----------------------------------------------------------------------- */

args:
|                                    { [] }
| LPAREN vs0=arg_list RPAREN vs=args { vs0 @ vs }

/* We use brackets to delimitate system expression and type variables,
   which creates a conflict if statement names can be empty, which
   we use in many examples.
   This use of brackets for both constructs may be reconsidered in
   the future; until then, we treat the case with an empty name
   separately and with limitations. */

statement_name:
| i=lsymb    { Some i }
| UNDERSCORE { None }

local_statement:
| system=system name=statement_name ty_vars=ty_args vars=args
  COLON f=term
   { let formula = Goal.Parsed.Local f in
     Goal.Parsed.{ name; ty_vars; vars; system; formula } }
| vars=args
  COLON f=term
   { let formula = Goal.Parsed.Local f in
     let name = None in
     let system = SystemExpr.P_SimplePair
                    SystemExpr.default_system_name in
     Goal.Parsed.{ name; ty_vars=[]; vars; system; formula } }

global_statement:
| system=bisystem name=statement_name ty_vars=ty_args vars=args
  COLON f=global_formula
   { let formula = Goal.Parsed.Global f in
     Goal.Parsed.{ name; ty_vars; vars; system; formula } }
| vars=args
  COLON f=global_formula
   { let formula = Goal.Parsed.Global f in
     let name = None in
     let system = SystemExpr.P_SimplePair
                    SystemExpr.default_system_name in
     Goal.Parsed.{ name; ty_vars=[]; vars; system; formula } }

obs_equiv_statement:
| s=bisystem n=statement_name
   { Goal.Parsed.{ name = n; system = s; ty_vars = []; vars = [];
                   formula = Goal.Parsed.Obs_equiv } }

goal_i:
|        GOAL s=local_statement  DOT { s }
|  LOCAL GOAL s=local_statement  DOT { s }
| GLOBAL GOAL s=global_statement DOT { s }
| EQUIV  s=obs_equiv_statement   DOT { s }
| EQUIV system=bisystem name=statement_name vars=args COLON b=loc(biframe) DOT
    { let f = L.mk_loc (L.loc b) (Theory.PEquiv (L.unloc b)) in
      Goal.Parsed.{ name; system; ty_vars = []; vars; formula = Global f } }

goal:
| goal=loc(goal_i) { goal }

option_param:
| TRUE  { Config.Param_bool true  }
| FALSE { Config.Param_bool false }
| n=ID  {
        if n = "true" then (Config.Param_bool true)
        else if n = "false" then (Config.Param_bool false)
        else Config.Param_string n   }
| i=INT { Config.Param_int i      }

set_option:
| SET n=ID EQ param=option_param DOT { (n, param) }

hint:
| HINT REWRITE id=lsymb DOT { Hint.Hint_rewrite id }

p_include:
| INCLUDE file=lsymb DOT  { file }

interactive:
| set=set_option     { Prover.ParsedSetOption set }
| decls=declarations { Prover.ParsedInputDescr decls }
| u=undo             { Prover.ParsedUndo u }
| tac=tactic         { Prover.ParsedTactic tac }
| PROOF              { Prover.ParsedProof }
| i=p_include        { Prover.ParsedInclude i }
| QED                { Prover.ParsedQed }
| ABORT              { Prover.ParsedAbort }
| g=goal             { Prover.ParsedGoal g }
| h=hint             { Prover.ParsedHint h }
| EOF                { Prover.EOF }
