%{
  open Squirrelcore
  module T  = Tactics
  module SE = SystemExpr

  module L = Location

  let sloc startpos endpos s =
    let loc = L.make startpos endpos in
    L.mk_loc loc s

  let mk_abstract loc s args =
    Tactics.Abstract (L.mk_loc loc s, args)
%}

%token <int> INT
%token <string> ID   /* general purpose identifier */
%token <string> PATH   /* general purpose path */
%token <string> LEFTINFIXSYMB    /* left infix function symbols */
%token <string> RIGHTINFIXSYMB   /* right infix function symbols */
%token <string> BANG

%token AT TRANS FRESH
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LBRACE RBRACE
%token QUOTE
%token LANGLE RANGLE
%token GAND GOR AND OR NOT TRUE FALSE 
%token EQ NEQ GEQ LEQ COMMA SEMICOLON COLON PLUS MINUS COLONEQ
%token XOR STAR UNDERSCORE QMARK TICK
%token LLET LET IN IF THEN ELSE FIND SUCHTHAT
%token TILDE DIFF SEQ
%token NEW OUT PARALLEL NULL
%token CHANNEL PROCESS
%token HASH AENC SENC SIGNATURE ACTION NAME ABSTRACT OP PREDICATE
%token TYPE FUN
%token MUTABLE SYSTEM SET
%token LEMMA THEOREM
%token INDEX MESSAGE BOOL BOOLEAN TIMESTAMP ARROW RARROW
%token EXISTS FORALL QUANTIF EQUIV DARROW DEQUIVARROW AXIOM
%token UEXISTS UFORALL
%token LOCAL GLOBAL
%token DOT SLASH BANGU SLASHEQUAL SLASHSLASH SLASHSLASHEQUAL ATSLASH
%token SHARP DOLLAR
%token GAME VAR RND RETURN
%token TIME WHERE WITH ORACLE EXN
%token PERCENT
%token TRY CYCLE REPEAT NOSIMPL HELP DDH CDH GDH CHECKFAIL ASSERT HAVE USE
%token REDUCE SIMPL AUTO
%token REWRITE REVERT CLEAR GENERALIZE DEPENDENT DEPENDS APPLY LOCALIZE CASE
%token SPLITSEQ CONSTSEQ MEMSEQ
%token BY FA CS INTRO AS DESTRUCT REMEMBER INDUCTION CRYPTO
%token PROOF QED RESET UNDO ABORT HINT
%token TACTIC
%token RENAME GPRF GCCA
%token INCLUDE PRINT SEARCH PROF
%token SMT
%token EOF

%nonassoc IN
%nonassoc QUANTIF
%right ARROW
%right DARROW 
%right DEQUIVARROW
%right AND OR
%right GAND GOR

%nonassoc EQ NEQ GEQ LEQ LANGLE RANGLE

%nonassoc empty_else
%nonassoc ELSE

%left SHARP

%right RIGHTINFIXSYMB
%left  LEFTINFIXSYMB

%left XOR

%nonassoc AT

%nonassoc tac_prec

%nonassoc BY
%left PLUS
%right SEMICOLON
%nonassoc REPEAT
%nonassoc TRY
%nonassoc NOSIMPL

%start declarations
%start top_formula
%start system_expr
%start top_process
%start interactive
%start top_proofmode
%start interactive_or_undo
%start top_proofmode_or_undo
%start top_global_formula
%type <Decl.declarations> declarations
%type <Theory.term> top_formula
%type <Theory.global_formula> top_global_formula
%type <SystemExpr.Parse.t> system_expr
%type <Process.Parse.t> top_process
%type <ProverLib.input> interactive
%type <ProverLib.input> top_proofmode
%type <ProverLib.input_or_undo> interactive_or_undo
%type <ProverLib.input_or_undo> top_proofmode_or_undo
%type <ProverTactics.AST.t> tac

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

(*------------------------------------------------------------------*)
(* Lists *)

%inline empty:
| { () }

%inline slist(X, S):
| l=separated_list(S, X) { l }

%inline slist1(X, S):
| l=separated_nonempty_list(S, X) { l }

(*------------------------------------------------------------------*)
%inline paren(X):
| LPAREN x=X RPAREN { x }

(*------------------------------------------------------------------*)
(* DH flags *)
dh_flag:
| DDH { Symbols.DH_DDH }
| CDH { Symbols.DH_CDH }
| GDH { Symbols.DH_GDH }

dh_flags:
| l=slist1(dh_flag, COMMA) { l }

(*------------------------------------------------------------------*)
(* Terms *)

lsymb:
| id=loc(ID) { id }

lpath:
| id=loc(PATH) { id }

%inline infix_s:
| EQ               { "=" , `Left }
| NEQ              { "<>", `Left }
| LEQ              { "<=", `Left }
| LANGLE           { "<" , `Left }
| GEQ              { ">=", `Left }
| RANGLE           { ">" , `Left }
| AND              { "&&", `Left }
| OR               { "||", `Left }
| s=LEFTINFIXSYMB  { s, `Left }
| s=RIGHTINFIXSYMB { s, `Right }
| XOR              { "xor", `Left }
| DARROW           { "=>" , `Left }
| DEQUIVARROW      { "<=>", `Left }

%inline infix_s0:
| s=infix_s { fst s }

(*------------------------------------------------------------------*)
/* non-ambiguous term */
sterm_i:
| id=lsymb                      { Theory.Symb id }
| UNDERSCORE                    { Theory.Tpat }

| DIFF LPAREN t=term COMMA t0=term RPAREN { Theory.Diff (t,t0) }

| SEQ LPAREN 
  vs=bnd_group_list(lval,ty_tagged) 
  DARROW t=term RPAREN                    { Theory.Quant (Seq,vs,t) }

| l=loc(NOT) f=sterm
    { let fsymb = L.mk_loc (L.loc l) "not" in
      Theory.mk_app_i (Theory.mk_symb fsymb) [f] }

| l=lloc(FALSE)  { Theory.Symb (L.mk_loc l "false") }

| l=lloc(TRUE)   { Theory.Symb (L.mk_loc l "true") }

| l=paren(slist1(term,COMMA))
    { match l with
      | [t] -> L.unloc t
      | _ -> Theory.Tuple l }

%inline quantif:
| EXISTS { Term.Exists }
| FORALL { Term.ForAll }

/* ambiguous term */
term_i:
| f=sterm_i                         { f }

| t=term AT ts=term                 { Theory.AppAt (t, ts) }
| t=sterm l=slist1(sterm,empty)     { Theory.App (t,l) }

| LANGLE t=term COMMA t0=term RANGLE
   { let fsymb = sloc $startpos $endpos "pair" in
     Theory.mk_app_i (Theory.mk_symb fsymb) [t;t0] }

| t=term s=loc(infix_s0) t0=term       
   { Theory.mk_app_i (Theory.mk_symb s) [t;t0] }

| t=term SHARP i=loc(INT)
    { Theory.Proj (i,t) }

| IF b=term THEN t=term t0=else_term
    { let fsymb = sloc $startpos $endpos "if" in
      Theory.mk_app_i (Theory.mk_symb fsymb) [b;t;t0] }

| FIND vs=bnds SUCHTHAT b=term IN t=term t0=else_term
                                 { Theory.Find (vs,b,t,t0) }

| FUN vs=ext_bnds_tagged DARROW f=term
                                 { Theory.Quant (Lambda,vs,f)  }

| q=quantif vs=ext_bnds_tagged COMMA f=term %prec QUANTIF
                                 { Theory.Quant (q,vs,f)  }

| LET v=lsymb ty=colon_ty? EQ t1=term IN t2=term
    { Theory.Let (v,t1,ty,t2) }

/* non-ambiguous term */
%inline else_term:
| %prec empty_else   { let loc = L.make $startpos $endpos in
                       let fsymb = L.mk_loc loc "zero" in
                       L.mk_loc loc (Theory.Symb fsymb) }
| ELSE t=term       { t }

sterm:
| t=loc(sterm_i) { t }

term:
| t=loc(term_i) { t }

(*------------------------------------------------------------------*)
term_list:
|                            { [] }
| t=paren(slist(term,COMMA)) { t }

(*------------------------------------------------------------------*)
/* simple lvalues: only support variable declarations */
simpl_lval:
| l=loc(UNDERSCORE)  { L.mk_loc (L.loc l) "_x" }
| l=lsymb            { l }

/* full lvalues */
%inline lval:
| l=simpl_lval                          { Theory.L_var l }
| LPAREN ids=slist1(lsymb,COMMA) RPAREN { Theory.L_tuple ids }

(*------------------------------------------------------------------*)
/* Auxiliary:
   Many binders with the same types: `x1,...,xN : type` */
%inline bnd_group(LVAL,TY):
| is=slist1(LVAL,COMMA) COLON k=TY { List.map (fun x -> x,k) is }

/* Auxiliary:
   many binder groups: `x1,...,xN1 : type1, ..., x1,...,xNL : typeL */
%inline bnd_group_list(LVAL,TY):
| args=slist1(bnd_group(LVAL,TY),COMMA) { List.flatten args }

(*------------------------------------------------------------------*)
/* Auxiliary: a single binder declarations */
%inline bnd:
| LPAREN l=bnd_group_list(simpl_lval,ty) RPAREN { l }
/* many binders, grouped  */

| x=simpl_lval    { [x, L.mk_loc (L.loc x) Theory.P_ty_pat] }
/* single binder `x`, unspecified type */

/* Many binder declarations, strict version
   for use when binder declarations are followed by COLON or COMMA. */
bnds_strict:
| l=slist(bnd, empty) { List.flatten l }

/* Many binder declarations, non-strict version with some added variants. */
bnds:
| bnds_strict                     { $1 }
| l=bnd_group_list(simpl_lval,ty) { l }

(*------------------------------------------------------------------*)
multi_term_bnd:
| LBRACE se_v=se_var COLON l=bnds RBRACE { se_v, l }

multi_term_bnds:
| l=slist(multi_term_bnd, empty) { l }

(*------------------------------------------------------------------*)
/* variable tags */
var_tags:
|                                             { []   }
| LBRACKET tags=slist1(lsymb, COMMA) RBRACKET { tags }

/* type with tags */
ty_tagged:
| k=ty tags=var_tags {k,tags}

(*------------------------------------------------------------------*)
/* Auxiliary: a single binder declarations with tags */
%inline bnd_tagged:
/* many binders, grouped  */
| LPAREN l=bnd_group_list(simpl_lval,ty_tagged) RPAREN { l }

/* single binder `x`, no argument */
| x=simpl_lval    { [x, (L.mk_loc (L.loc x) Theory.P_ty_pat, [])] }

/* Many binder declarations with tags. */
bnds_tagged:
| l=slist(bnd_tagged, empty) { List.flatten l }

(*------------------------------------------------------------------*)
/* Auxiliary: a single binder declarations with tags with full lvalues */
%inline ext_bnd_tagged:
/* many binders, grouped  */
| LPAREN l=bnd_group_list(lval,ty_tagged) RPAREN { l }

/* single binder `x`, no argument */
| x=simpl_lval    { [Theory.L_var x, (L.mk_loc (L.loc x) Theory.P_ty_pat, [])] }

/* Many binder declarations with tags (see bnds_strict). */
ext_bnds_tagged_strict:
| l=slist(ext_bnd_tagged, empty)   { List.flatten l }

ext_bnds_tagged:
| ext_bnds_tagged_strict           { $1 }
| v=simpl_lval COLON ty=ty_tagged  { [Theory.L_var v, ty] }

(*------------------------------------------------------------------*)
top_formula:
| f=term EOF                    { f }

(*------------------------------------------------------------------*)
(* Processes *)

top_process:
| p=process EOF                    { p }

colon_ty:
| COLON t=ty { t }


(* identifier with '$' allowed at the beginning or end *) 
%inline alias_name:
| s=ID { s }
| DOLLAR s=ID { "$" ^ s }
| s=ID DOLLAR { "$" ^ s }

process_i:
| NULL                               { Process.Parse.Null }
| LPAREN ps=processes_i RPAREN       { ps }
| id=lsymb terms=term_list           { Process.Parse.Apply (id,terms) }
| id=loc(alias_name) COLON p=process { Process.Parse.Alias (p,id) }

| NEW id=lsymb ty=colon_ty? SEMICOLON p=process
    { let ty = match ty with
        | Some ty -> ty
        | None -> L.mk_loc (L.loc id) Theory.P_message
      in
      Process.Parse.New (id,ty,p) }

| IN LPAREN c=lsymb COMMA id=lsymb RPAREN p=process_cont
    { Process.Parse.In (c,id,p) }

| OUT LPAREN c=lsymb COMMA t=term RPAREN p=process_cont
    { Process.Parse.Out (c,t,p) }

| IF f=term THEN p=process p0=else_process
    { Process.Parse.Exists ([],f,p,p0) }

| FIND is=opt_indices SUCHTHAT f=term IN p=process p0=else_process
    { Process.Parse.Exists (is,f,p,p0) }

| LET id=lsymb ty=colon_ty? EQ t=term IN p=process
    { Process.Parse.Let (id,t,ty,p) }

| id=lsymb args=term_list COLONEQ t=term p=process_cont
    { Process.Parse.Set (id,args,t,p) }

| s=loc(BANG) p=process { Process.Parse.Repl (s,p) }

process:
| p=loc(process_i) { p }

processes_i:
| p=process_i                             { p }
| p=process PARALLEL ps=loc(processes_i)  { Process.Parse.Parallel (p,ps) }

process_cont:
|                                { let loc = L.make $startpos $endpos in
                                   L.mk_loc loc Process.Parse.Null }
| SEMICOLON p=process            { p }

else_process:
| %prec empty_else               { let loc = L.make $startpos $endpos in
                                   L.mk_loc loc Process.Parse.Null }
| ELSE p=process                 { p }

opt_indices:
|                                   { [] }
| id=lsymb                          { [id] }
| id=lsymb COMMA ids=opt_indices    { id::ids }

/* type variable */
ty_var:
| TICK id=lsymb     { id }

/* system expression variable */
se_var:
| ll=lloc(SET)   { L.mk_loc ll "set" }
| ll=lloc(EQUIV) { L.mk_loc ll "equiv" }
| id=lsymb       { id }

(*------------------------------------------------------------------*)
/* general types */

ty_i:
| ty=sty_i                          { ty }
| t1=ty ARROW t2=ty                 { Theory.P_fun (t1, t2) }
| t1=sty STAR tys=slist1(sty, STAR) { Theory.P_tuple (t1 :: tys) }

sty_i:
| MESSAGE                        { Theory.P_message }
| INDEX                          { Theory.P_index }
| TIMESTAMP                      { Theory.P_timestamp }
| BOOLEAN                        { Theory.P_boolean }
| BOOL                           { Theory.P_boolean }
| tv=ty_var                      { Theory.P_tvar tv }
| l=lsymb                        { Theory.P_tbase l }
| LPAREN ty=ty_i RPAREN          { ty }
| UNDERSCORE                     { Theory.P_ty_pat }

sty:
| ty=loc(sty_i) { ty }

ty:
| ty=loc(ty_i) { ty }

(*------------------------------------------------------------------*)
se_info:
| i=lsymb { i }

se_bnd:
| v=se_var                                          { v, [] }
| v=se_var LBRACKET l=slist(se_info,empty) RBRACKET { v, l  }

%inline se_bnds:
/* |                                        { [] } */
| LBRACE ids=slist(se_bnd,empty) RBRACE { ids }

(*------------------------------------------------------------------*)
/* crypto assumption typed space */
c_ty:
| l=lsymb COLON ty=ty { Decl.{ cty_space = l;
                                      cty_ty    = ty; } }

/* crypto assumption typed space */
c_tys:
| WHERE list=slist1(c_ty, empty) { list }
|                                { [] }

ty_args:
|                                            { [] }
| LBRACKET ids=slist1(ty_var,empty) RBRACKET { ids }

bty_info:
| info=lsymb { info }

bty_infos:
| LBRACKET l=slist(bty_info,COMMA) RBRACKET { l }
|                                           { [] }

lsymb_decl:
| id=lsymb                     { `Prefix, id }
| LPAREN s=loc(infix_s) RPAREN 
          { let loc = L.loc s in
            let k = snd @@ L.unloc s in
            let s = fst @@ L.unloc s in
            `Infix k, L.mk_loc loc s }

%inline projs:
|                                     { None }
| LBRACE l=slist(lsymb, empty) RBRACE { Some l }

(*------------------------------------------------------------------*)
predicate_body:
| EQ form=global_formula { form }

(*------------------------------------------------------------------*)
system_modifier:
| RENAME gf=global_formula
    { Decl.Rename gf }

| GCCA args=bnds_strict COMMA enc=term
    { Decl.CCA (args, enc) }

| GPRF args=bnds_strict COMMA hash=term
    { Decl.PRF (args, hash) }

| GPRF TIME args=bnds_strict COMMA hash=term
    { Decl.PRFt (args, hash) }

| REWRITE p=rw_args
    { Decl.Rewrite p }

(*------------------------------------------------------------------*)
declaration_i:
| HASH e=lsymb ctys=c_tys
                          { Decl.Decl_hash (e, None, ctys) }

| HASH e=lsymb WITH ORACLE f=term
                          { Decl.Decl_hash (e, Some f, []) }

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

| h=dh_flags g=lsymb COMMA ei=lsymb_decl ctys=c_tys
    { let e, f_info = ei in
      Decl.Decl_dh (h, g, (f_info, e), None, ctys) }

| h=dh_flags g=lsymb COMMA ei=lsymb_decl COMMA mm=lsymb_decl ctys=c_tys
    { let e, f_info = ei in
      let m, m_info = mm in
      Decl.Decl_dh (h, g, (f_info, e), Some (m_info, m), ctys) }

| NAME e=lsymb COLON ty=ty
                          { Decl.Decl_name (e, ty) }

| ACTION e=lsymb COLON a_arity=int
                          { Decl.Decl_action { a_name = e; a_arity; } }

| TYPE e=lsymb infos=bty_infos
                          { Decl.Decl_bty { bty_name = e; bty_infos = infos; } }

| ABSTRACT e=lsymb_decl a=ty_args COLON t=ty
    { let symb_type, name = e in
      Decl.(Decl_abstract
              { name      = name;
                symb_type = symb_type;
                ty_args   = a;
                abs_tys   = t; }) }


| PREDICATE e=lsymb_decl
  tyargs=ty_args sebnds=se_bnds
  multi_args=multi_term_bnds
  simpl_args=bnds
  body=predicate_body? 
    { let symb_type, name = e in
      Decl.(Decl_predicate
              { pred_name       = name;
                pred_symb_type  = symb_type;
                pred_tyargs     = tyargs;
                pred_se_args    = sebnds;
                pred_multi_args = multi_args;
                pred_simpl_args = simpl_args;
                pred_body       = body; }) }

| OP e=lsymb_decl tyargs=ty_args args=ext_bnds_tagged_strict tyo=colon_ty? EQ t=term
    { let symb_type, name = e in
      Decl.(Decl_operator
              { op_name      = name;
                op_symb_type = symb_type;
                op_tyargs    = tyargs;
                op_args      = args;
                op_tyout     = tyo;
                op_body      = t; }) }

| MUTABLE name=lsymb args=bnds_strict out_ty=colon_ty? EQ init_body=term
                          { Decl.Decl_state {name; args; out_ty; init_body; }}

| CHANNEL e=lsymb         { Decl.Decl_channel e }

| PROCESS id=lsymb projs=projs args=bnds EQ proc=process
                          { Decl.Decl_process {id; projs; args; proc} }

|        AXIOM s=local_statement  { Decl.Decl_axiom s }
|  LOCAL AXIOM s=local_statement  { Decl.Decl_axiom s }
| GLOBAL AXIOM s=global_statement { Decl.Decl_axiom s }

| SYSTEM sprojs=projs p=process
                          { Decl.(Decl_system { sname = None;
                                                sprojs;
                                                sprocess = p}) }

| SYSTEM LBRACKET id=lsymb RBRACKET sprojs=projs p=process
                          { Decl.(Decl_system { sname = Some id;
                                                sprojs;
                                                sprocess = p}) }

| SYSTEM id=lsymb EQ from_sys=system_expr WITH modifier=system_modifier
    { Decl.(Decl_system_modifier
              { from_sys = from_sys;
                modifier;
                name = id}) }

 | g=game { Decl.Decl_game g }

declaration_no_concat_i:
| TACTIC lsymb EQ tac                     { Decl.Tactic ($2,$4) }

declaration:
| ldecl=loc(declaration_i)                { ldecl }

declaration_no_concat:
| ldecl=loc(declaration_no_concat_i)      { ldecl }

declaration_list:
| decl=declaration                        { [decl] }
| decl=declaration_no_concat              { [decl] }
| decl=declaration decls=declaration_list { decl :: decls }

declarations:
| decls=declaration_list DOT { decls }

(*------------------------------------------------------------------*)
/* games */

/* random samplings declarations (global or oracle) */
game_var_rnd:
| RND v=lsymb COLON ty=ty SEMICOLON
    { Crypto.Parse.{ vr_name = v; vr_ty = ty; } } 

game_var_rnds:
| l=slist(game_var_rnd, empty ) { l }

/* variable declarations (in global (mutable) or oracle (non-mutable))  */
game_var_decl:
| VAR v=lsymb ty=colon_ty? EQ t=term SEMICOLON
    { Crypto.Parse.{ vd_name = v; vd_ty = ty; vd_init = t; } } 

game_var_decls:
| l=slist(game_var_decl, empty) { l }

/* an update in an oracle */
game_update:
| id=lsymb COLONEQ t=term SEMICOLON { (id,t) }

game_updates:
| l=slist(game_update, empty) { l }

oracle_ret:
| RETURN ret=term SEMICOLON? { ret }

oracle_body:
| rnds=game_var_rnds vars=game_var_decls updates=game_updates ret=oracle_ret?
{ Crypto.Parse.{ 
    bdy_rnds    = rnds; 
    bdy_lvars   = vars; 
    bdy_updates = updates; 
    bdy_ret     = ret; 
  } 
}

/* an oracle declaration */
oracle_decl:
| ORACLE n=lsymb args=bnds_strict ty=colon_ty? EQ LBRACE body=oracle_body RBRACE
    { Crypto.Parse.{ o_name = n; o_args = args; o_tyout = ty; o_body = body; } }

oracle_decls:
| l=slist(oracle_decl, empty) { l }

game:
| GAME n=lsymb EQ LBRACE
    rnds=game_var_rnds
    vars=game_var_decls 
    orcls=oracle_decls 
  RBRACE
    { Crypto.Parse.{ 
        g_name    = n; 
        g_rnds    = rnds; 
        g_gvar    = vars; 
        g_oracles = orcls;
      } 
    }

(*------------------------------------------------------------------*)
tactic_param:
| f=term %prec tac_prec  { TacticsArgs.Theory f }
| i=loc(INT)             { TacticsArgs.Int_parsed i }

tactic_params:
|                                       { [] }
| t=tactic_param                        { [t] }
| t=tactic_param COMMA ts=tactic_params { t::ts }

(*------------------------------------------------------------------*)
rw_mult:
| i=int BANGU { TacticsArgs.Exact i }
| BANGU       { TacticsArgs.Many }
| QMARK       { TacticsArgs.Any }
|             { TacticsArgs.Once }

rw_dir:
|       { `LeftToRight }
| MINUS { `RightToLeft }

rw_type:
| pt=spt                        { `Rw pt }
| SLASH s=lsymb_decl            { `Expand (snd s) }
| SLASH l=lloc(STAR)            { `ExpandAll l }

expnd_type:
| ATSLASH s=lsymb_decl  { `Expand (snd s) }
| ATSLASH l=lloc(STAR)  { `ExpandAll l }

rw_item:
| m=rw_mult d=loc(rw_dir) t=rw_type  { TacticsArgs.{ rw_mult = m;
                                                     rw_dir = d;
                                                     rw_type = t; } }

rw_equiv_item:
| d=loc(rw_dir) pt=pt  { TacticsArgs.{ rw_mult = TacticsArgs.Once;
                                         rw_dir = d;
                                         rw_type = `Rw pt; } }

expnd_item:
| d=loc(rw_dir) t=expnd_type  { TacticsArgs.{ rw_mult = TacticsArgs.Once;
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
| IN l=slist1(single_target,COMMA) { `HypsOrDefs l }
| IN STAR                          { `All }

(*------------------------------------------------------------------*)
fa_arg:
| d=rw_mult t=term %prec tac_prec { (d,t) }

(*------------------------------------------------------------------*)
apply_in:
|             { None }
| IN id=lsymb { Some id }

(*------------------------------------------------------------------*)
naming_pat:
| UNDERSCORE  { TacticsArgs.Unnamed }
| QMARK       { TacticsArgs.AnyName }
| id=ID       { TacticsArgs.Named id }

and_or_ip:
| LBRACKET s=simpl_ip          ips=slist(simpl_ip, empty)    RBRACKET
                    { TacticsArgs.And (s :: ips) }
| LBRACKET s=simpl_ip PARALLEL ips=slist(simpl_ip, PARALLEL) RBRACKET
                    { TacticsArgs.Or  (s :: ips) }
| LBRACKET RBRACKET { TacticsArgs.Split }

rewrite_ip:
| ARROW  { `LeftToRight }
| RARROW { `RightToLeft }

simpl_ip:
| n_ip=naming_pat  { TacticsArgs.SNamed n_ip }
| ao_ip=and_or_ip { TacticsArgs.SAndOr ao_ip }
| d=loc(rewrite_ip) { TacticsArgs.Srewrite d }

s_item_body:
| l=loc(SLASHSLASH)      { TacticsArgs.Tryauto      (L.loc l)}
| l=loc(SLASHEQUAL)      { TacticsArgs.Simplify     (L.loc l)}
| l=loc(SLASHSLASHEQUAL) { TacticsArgs.Tryautosimpl (L.loc l)}

%inline s_item:
| s=s_item_body { s,[] }
| LBRACKET s=s_item_body a=named_args RBRACKET { s, a }

/* same as a [s_item], but without arguments */
s_item_noargs:
| s=s_item_body { s,[] }

clear_ip:
| LBRACE l=slist1(lsymb, empty) RBRACE { l }

intro_pat:
| l=clear_ip    { TacticsArgs.SClear l }
| s=s_item      { TacticsArgs.SItem (s) }
| l=loc(STAR)   { TacticsArgs.Star  (L.loc l)}
| l=loc(RANGLE) { TacticsArgs.StarV (L.loc l)}
| pat=simpl_ip { TacticsArgs.Simpl pat }
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

as_n_ips:
| AS n_ips=slist1(naming_pat, empty) { n_ips }

%inline sel_tac:
| s=selector COLON r=tac { (s,r) }

sel_tacs:
| l=slist1(sel_tac,PARALLEL) { l }

(*------------------------------------------------------------------*)
pt_arg:
| t=sterm                        { Theory.PTA_term t }
/* Note: some terms parsed as [sterm] may be resolved as [PTA_sub]
   later, using the judgement hypotheses. */

| PERCENT LPAREN pt=pt RPAREN  { Theory.PTA_sub pt }

(*------------------------------------------------------------------*)
/* ambiguous pt */
pt_cnt:
| pt=spt_cnt  { pt }

| head=spt args=slist1(pt_arg,empty)
    { let pta_loc = L.make $startpos $endpos in
      let app = Theory.{ pta_head = head; pta_args = args; pta_loc; } in
      Theory.PT_app app }

pt:
| pt=loc(pt_cnt) { pt }

(*------------------------------------------------------------------*)
/* non-ambiguous pt */
spt_cnt:
| head=lsymb   { Theory.PT_symb head }
| PERCENT LOCAL LPAREN pt=pt RPAREN { Theory.PT_localize pt }
| LPAREN pt=pt_cnt RPAREN
    { pt }

spt:
| pt=loc(spt_cnt) { pt }

(*------------------------------------------------------------------*)
/* legacy syntax for use tactic */
pt_use_tac:
| pt=spt { pt }

| head=spt WITH args=slist1(tac_term,COMMA)
    { let pta_loc = L.make $startpos $endpos in
      let args = List.map (fun x -> Theory.PTA_term x) args in
      let app = Theory.{ pta_head = head; pta_args = args; pta_loc; } in
      L.mk_loc pta_loc (Theory.PT_app app) }

(*------------------------------------------------------------------*)
constseq_arg:
| LPAREN b=term RPAREN t=sterm { (b,t) }

(*------------------------------------------------------------------*)
trans_arg_item:
| i=loc(int) COLON t=term %prec tac_prec { i,t }

trans_arg:
| annot=system_annot { TacticsArgs.TransSystem (`Global, annot) }
| l=slist1(trans_arg_item, COMMA) { TacticsArgs.TransTerms l }

(*------------------------------------------------------------------*)
fresh_arg:
| i=loc(int) { TacticsArgs.FreshInt i }
| l=lsymb    { TacticsArgs.FreshHyp l }

(*------------------------------------------------------------------*)
%inline generalize_dependent:
| GENERALIZE DEPENDENT { }

%inline dependent_induction:
| DEPENDENT INDUCTION { }

%inline rewrite_equiv:
| REWRITE EQUIV { }

(*------------------------------------------------------------------*)
/* local or global formula */
%inline any_term:
  | f=term           { Theory.Local f }
  | g=global_formula { Theory.Global g }

tac_any_term:
| f=any_term %prec tac_prec { f }

(*------------------------------------------------------------------*)
/* have ip (with AS keyword) for legacy usage (no support for s_items) */
as_have_ip:
| AS ip=simpl_ip { ([],ip,[]) }

s_item_noargs_list:
| l=slist(s_item_noargs,empty) { l }

/* FIXME: allow [s_item] with arguments */
have_ip:
| pre=s_item_noargs_list ip=simpl_ip post=s_item_noargs_list { (pre, ip, post) }

%inline have_tac:
| l=lloc(ASSERT) p=tac_term ip=as_have_ip? 
    { mk_abstract l "have" [TacticsArgs.Have (ip, Theory.Local p)] }

| l=lloc(HAVE) ip=have_ip COLON p=tac_any_term 
    { mk_abstract l "have" [TacticsArgs.Have (Some ip, p)] }

(*------------------------------------------------------------------*)
/* crypto arguments */

crypto_arg_extra:
| COLON bnds=bnds_strict COMMA term=term { bnds, term }

crypto_arg:
| LPAREN glob_sample=lsymb COLON term=term extra=crypto_arg_extra? RPAREN
    { let bnds, cond = Utils.omap_dflt (None,None) (fun (x,y) -> Some x, Some y) extra in
      TacticsArgs.{glob_sample ; term; bnds; cond; } }

(*------------------------------------------------------------------*)
/* Named arguments for tactics */
/* Here we use a "lexical feedback" hack to make it possible to
   parse keywords as lsymbs. */

enable_kwd_as_id:
| { Feedback.enable_keywords_as_ids () }
disable_kwd_as_id:
| { Feedback.disable_keywords_as_ids () }

named_arg:
| enable_kwd_as_id TILDE l=label disable_kwd_as_id
  { TacticsArgs.NArg l }
| enable_kwd_as_id TILDE l=label COLON
  LBRACKET ll=slist(label,COMMA) RBRACKET
  disable_kwd_as_id
  { TacticsArgs.NList (l,ll) }
| enable_kwd_as_id TILDE l=label COLON a=label disable_kwd_as_id
  { TacticsArgs.NList (l,[a]) }

label:
| l=lsymb { l }

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
  | l=lloc(BY) t=tac                   { T.By (t,l) }
  | l=tac PLUS r=tac                   { T.OrElse [l;r] }
  | TRY l=tac                          { T.Try l }
  | REPEAT t=tac                       { T.Repeat t }
  | id=lsymb t=tactic_params           { mk_abstract (L.loc id) (L.unloc id) t }

  (* Special cases for tactics whose names are not parsed as ID
   * because they are reserved. *)

  (* Crypto tactic *)
  | l=lloc(CRYPTO) game=lsymb args=slist(crypto_arg,empty)
    { mk_abstract l "crypto" [TacticsArgs.Crypto (game,args)] }

  (* Case *)
  | id=loc(CASE) a=named_args t=tac_term
    { mk_abstract (L.loc id) "case" [TacticsArgs.Named_args a; Theory t] }

  (* SMT *)
  | id=loc(SMT) a=named_args
    { mk_abstract (L.loc id) "smt" [TacticsArgs.Named_args a] }

  (* Case_Study, equiv tactic, patterns *)
  | l=lloc(CS) t=tac_term
    { mk_abstract l "cs" [TacticsArgs.Theory t] }

  (* Case_Study, equiv tactic, patterns with element number *)
  | l=lloc(CS) t=term IN i=loc(int)
    { mk_abstract l "cs" [TacticsArgs.Theory t; 
                          TacticsArgs.Int_parsed i] }

  (* FA, equiv tactic, patterns *)
  | l=lloc(FA) args=slist1(fa_arg, COMMA)
    { mk_abstract l "fa" [TacticsArgs.Fa args] }

  (* FA, equiv tactic, frame element number *)
  | l=lloc(FA) i=loc(int)
    { mk_abstract l "fa" [TacticsArgs.Int_parsed i] }

  (* FA, trace tactic *)
  | l=lloc(FA) 
    { mk_abstract l "fa" [] }

  | l=lloc(INTRO) p=intro_pat_list
    { mk_abstract l "intro" [TacticsArgs.IntroPat p] }

  | t=tac l=lloc(DARROW) p=intro_pat_list
    { T.AndThen [t; mk_abstract l "intro" [TacticsArgs.IntroPat p]] }

  | l=lloc(DESTRUCT) i=lsymb
    { mk_abstract l "destruct" [TacticsArgs.String_name i] }

  | l=lloc(DESTRUCT) i=lsymb AS p=and_or_ip
    { mk_abstract l "destruct" [TacticsArgs.String_name i;
                                TacticsArgs.AndOrPat p] }

  | l=lloc(LOCALIZE) i=lsymb AS p=naming_pat
    { mk_abstract l "localize" [TacticsArgs.String_name i;
                                TacticsArgs.NamingPat p] }

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

  (*------------------------------------------------------------------*)
  /* assert that we have a formula */
  | t=have_tac { t }

  | t=have_tac l=lloc(BY) t1=tac
    { T.AndThenSel (t, [[1], T.By (t1,l)]) }

  | l=lloc(USE) pt=pt_use_tac ip=as_have_ip?
    { mk_abstract l "have" [TacticsArgs.HavePt (pt, ip, `IntroImpl)] }

  (*------------------------------------------------------------------*)
  /* assert a proof term */
  | l=lloc(HAVE) ip=have_ip? COLONEQ pt=pt 
    { mk_abstract l "have" [TacticsArgs.HavePt (pt, ip, `None)] }

  (*------------------------------------------------------------------*)
  | l=lloc(TRANS) arg=trans_arg
    { mk_abstract l "trans" [TacticsArgs.Trans arg] }

  | l=lloc(FRESH) a=named_args arg=fresh_arg
    { mk_abstract l "fresh" [TacticsArgs.Fresh (a,arg)] }

  | l=lloc(AUTO) a=named_args 
    { mk_abstract l "auto" [TacticsArgs.Named_args a] }

  | l=lloc(SIMPL) a=named_args 
    { mk_abstract l "simpl" [TacticsArgs.Named_args a] }

  | l=lloc(REDUCE) a=named_args 
    { mk_abstract l "reduce" [TacticsArgs.Named_args a] }

  | l=lloc(REWRITE) p=rw_args w=in_target
    { mk_abstract l "rewrite" [TacticsArgs.RewriteIn (p, w)] }

  | l=lloc(rewrite_equiv) p=rw_equiv_item
    { mk_abstract l "rewrite equiv" [TacticsArgs.RewriteEquiv (p)] }

  | l=lloc(APPLY) a=named_args t=pt w=apply_in
    { mk_abstract l "apply" [TacticsArgs.ApplyIn (a, t, w)] }

  | l=lloc(SPLITSEQ) i=loc(INT) COLON LPAREN ht=term RPAREN dflt=sterm?
    { mk_abstract l "splitseq" [TacticsArgs.SplitSeq (i, ht, dflt)] }

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

  | l=lloc(CDH) i1=tac_term COMMA g=tac_term
    { mk_abstract l "cdh"
         [TacticsArgs.Theory i1;
          TacticsArgs.Theory g] }

  | l=lloc(GDH) i1=tac_term COMMA g=tac_term
    { mk_abstract l "gdh"
         [TacticsArgs.Theory i1;
          TacticsArgs.Theory g] }

undo:
| UNDO i=INT DOT                      { i }

tactic:
| t=tac DOT                           { t }

biframe:
| ei=term                   { [ei] }
| ei=term COMMA eis=biframe { ei::eis }

/* ----------------------------------------------------------------------- */
%inline quant:
| UFORALL { Theory.PForAll }
| UEXISTS { Theory.PExists }

se_args:
| LBRACE l=slist(system_expr,empty) RBRACE { l  }
|                                          { [] }

global_formula_i:
| LBRACKET f=term RBRACKET         { Theory.PReach f }
| TILDE LPAREN e=biframe RPAREN    { Theory.PEquiv e }
| EQUIV LPAREN e=biframe RPAREN    { Theory.PEquiv e }
| LPAREN f=global_formula_i RPAREN { f }

| f=global_formula ARROW f0=global_formula { Theory.PImpl (f,f0) }

| q=quant vs=bnds_tagged COMMA f=global_formula %prec QUANTIF
                                   { Theory.PQuant (q,vs,f)  }

| f1=global_formula GAND f2=global_formula
                                   { Theory.PAnd (f1, f2) }
| f1=global_formula GOR f2=global_formula
                                   { Theory.POr (f1, f2) }

| LLET v=lsymb ty=colon_ty? EQ t=term IN f=global_formula
    { Theory.PLet (v,t,ty,f) }
  
| DOLLAR LPAREN g=a_global_formula_i RPAREN { g }

/* ambiguous global formula, in the sens that it can be confused 
   with a local term */
a_global_formula_i:
| name=lsymb se_args=se_args args=slist(sterm, empty)
    { Theory.PPred Theory.{ name; se_args; args; }  }

| t=sterm name=loc(infix_s0) se_args=se_args t0=sterm 
    { Theory.PPred Theory.{ name; se_args; args = [t; t0]; }  }

/* ----------------------------------------------------------------------- */
/* a_global_formula: */
/* | f=loc(a_global_formula_i) { f } */

global_formula:
| f=loc(global_formula_i) { f }

top_global_formula:
| f=global_formula EOF { f }

/* -----------------------------------------------------------------------
 * Systems
 * ----------------------------------------------------------------------- */

system_item:
| i=lsymb               { SE.Parse.{ alias = None; system = i; projection = None   } }
| i=lsymb SLASH p=lsymb { SE.Parse.{ alias = None; system = i; projection = Some p } }

system_item_list:
| i=system_item                          {  [i] }
| i=system_item COMMA l=system_item_list { i::l }

system_expr:
| LBRACKET s=loc(system_item_list) RBRACKET   { s }

system_annot_cnt:
|                                             { SE.Parse.NoSystem }
| LBRACKET l=loc(system_item_list) RBRACKET   { SE.Parse.System l }
| LBRACKET
    SET COLON s=loc(system_item_list) SEMICOLON
  EQUIV COLON p=loc(system_item_list)
  RBRACKET                                    { SE.Parse.Set_pair (s,p) }

system_annot:
| a=loc(system_annot_cnt) { a }

/* -----------------------------------------------------------------------
 * Statements and goals
 * ----------------------------------------------------------------------- */

statement_name:
| i=lsymb    { Some i }
| UNDERSCORE { None }

local_statement:
| s=system_annot name=statement_name ty_vars=ty_args vars=bnds_tagged
  COLON f=term
   { let system = `Local, s in
     let formula = Goal.Parsed.Local f in
     Goal.Parsed.{ name; ty_vars; vars; system; formula } }

global_statement:
| s=system_annot name=statement_name ty_vars=ty_args vars=bnds_tagged
  COLON f=global_formula
   { let formula = Goal.Parsed.Global f in
     let system = `Global, s in
     Goal.Parsed.{ name; ty_vars; vars; system; formula } }

obs_equiv_statement:
| s=system_annot n=statement_name
   { let system = `Global, s in
     Goal.Parsed.{ name = n; system; ty_vars = []; vars = [];
                   formula = Goal.Parsed.Obs_equiv } }

lemma_head:
| LEMMA   {}
| THEOREM {}
 
lemma_i:
|        lemma_head s=local_statement  DOT { s }
|  LOCAL lemma_head s=local_statement  DOT { s }
| GLOBAL lemma_head s=global_statement DOT { s }
| EQUIV  s=obs_equiv_statement         DOT { s }
| EQUIV s=system_annot name=statement_name vars=bnds_tagged COLON b=loc(biframe) DOT
    { let f = L.mk_loc (L.loc b) (Theory.PEquiv (L.unloc b)) in
      let system = `Global, s in
      Goal.Parsed.{ name; system; ty_vars = []; vars; formula = Global f } }

lemma:
| l=loc(lemma_i) { l }

(*------------------------------------------------------------------*)
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

(*------------------------------------------------------------------*)
hint:
| HINT REWRITE id=lsymb DOT { Hint.Hint_rewrite id }
| HINT SMT     id=lsymb DOT { Hint.Hint_smt     id }

(*------------------------------------------------------------------*)
include_params:
| LBRACKET l=slist(lsymb, COMMA) RBRACKET { l }
|                                         { [] }

p_include:
| INCLUDE l=include_params QUOTE th=lpath QUOTE DOT
    { ProverLib.{ th_name = ProverLib.Path th; params = l; } }
| INCLUDE l=include_params th=lsymb DOT
    { ProverLib.{ th_name = ProverLib.Name th; params = l; } }

(*------------------------------------------------------------------*)
query:
| HELP DOT                       { ProverLib.Help }
| PROF DOT                       { ProverLib.Prof }
(* print *)
| PRINT SYSTEM l=system_expr DOT { ProverLib.(Print (Pr_system (Some l))) }
| PRINT l=lsymb DOT              { ProverLib.(Print (Pr_any l)) }
| PRINT DOT                      { ProverLib.(Print (Pr_system None)) }
(* search *)
| SEARCH t=any_term IN s=system_expr DOT
                                 { ProverLib.(Search (Srch_inSys (t,s))) }
| SEARCH t=any_term DOT          { ProverLib.(Search (Srch_term t)) }

(*------------------------------------------------------------------*)
interactive_or_undo:
| u=undo             { ProverLib.Undo u }
| i=interactive      { ProverLib.Input i }

interactive:
| decls=declarations { ProverLib.(InputDescr decls) }
| set=set_option     { ProverLib.(SetOption set) }
| h=hint             { ProverLib.(Hint h) }
| q=query            { q }
| i=p_include        { ProverLib.(Include i) }
| g=lemma            { ProverLib.(Goal g) }
| PROOF              { ProverLib.Proof }
| RESET              { ProverLib.Reset }
| EOF                { ProverLib.EOF }

bullet:
| MINUS              { "-" }
| PLUS               { "+" }
| STAR               { "*" }
| s=RIGHTINFIXSYMB   { s }
| s=LEFTINFIXSYMB    { s }

brace:
| LBRACE             { `Open }
| RBRACE             { `Close }

bulleted_tactic:
| bullet bulleted_tactic { (ProverLib.Bullet $1) :: $2 }
| brace  bulleted_tactic { (ProverLib.Brace  $1) :: $2 }
| tactic                 { [ ProverLib.BTactic $1 ] }
| DOT                    { [] }

top_proofmode_or_undo:
| u=undo                 { ProverLib.Undo u }
| i=top_proofmode        { ProverLib.Input i }

top_proofmode:
| q=query            { q }
| t=bulleted_tactic  { ProverLib.(Tactic t) }
| ABORT              { ProverLib.Abort }
| QED                { ProverLib.Qed }
| RESET              { ProverLib.Reset }
| EOF                { ProverLib.EOF }
