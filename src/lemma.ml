open Utils

module L = Location

type lsymb = Theory.lsymb
               
(*------------------------------------------------------------------*)
(** An top-level axiom or proved lemma. *)

type lemma = { 
  stmt : Goal.statement;
  kind : [`Axiom | `Lemma];
} 

type Symbols.data += Lemma of lemma

(*------------------------------------------------------------------*)
let pp_kind fmt = function
  | `Axiom -> Printer.kw `Goal fmt "axiom"
  | `Lemma -> Printer.kw `Goal fmt "goal"

let pp fmt lem =
  Fmt.pf fmt "@[<v 2>%a %a@]" 
    pp_kind lem.kind Goal.pp_statement lem.stmt

(*------------------------------------------------------------------*)
let as_lemma : Symbols.data -> lemma = function
  | Lemma s -> s
  | _ -> assert false

(*------------------------------------------------------------------*)
let find gname table : lemma =
  as_lemma (Symbols.Lemma.data_of_lsymb gname table) 

let find_opt gname table : lemma option =
  if not (Symbols.Lemma.mem_lsymb gname table)
  then None
  else Some (find gname table)

(*------------------------------------------------------------------*)
let find_stmt_reach gname table =
  Goal.to_reach_statement ~loc:(L.loc gname) (find gname table).stmt

let find_stmt_equiv gname table =
  Goal.to_equiv_statement ~loc:(L.loc gname) (find gname table).stmt

(*------------------------------------------------------------------*)
let find_stmt gname table : Goal.statement    = (find gname table).stmt
let find_kind gname table : [`Axiom | `Lemma] = (find gname table).kind

(*------------------------------------------------------------------*)
let mem gname table : bool =
  Symbols.Lemma.mem_lsymb gname table

let mem_reach gname table : bool =
  match find_opt gname table with
  | None -> false
  | Some s -> Goal.is_reach_statement s.stmt

let mem_equiv gname table : bool =
  match find_opt gname table with
  | None -> false
  | Some s -> Goal.is_equiv_statement s.stmt

(*------------------------------------------------------------------*)
let add_lemma
    ?(loc = L._dummy)
    (kind : [`Axiom | `Lemma]) (gconcl : Goal.statement)
    (table : Symbols.table) : Symbols.table
  =
  let lem = { stmt = gconcl; kind } in
  let data = Lemma lem in
  let table, _ =
    Symbols.Lemma.declare_exact table (L.mk_loc loc gconcl.Goal.name) ~data ()
  in
  Printer.pr "%a@;" pp lem;
  table

(*------------------------------------------------------------------*)
let print_all fmt table : unit =
  Symbols.Lemma.iter (fun _ _ data ->
      let g = as_lemma data in
      Fmt.pf fmt "%s: %a@;" g.stmt.name Equiv.Any.pp g.stmt.formula
    ) table


(*------------------------------------------------------------------*)
(** {2 Depends, Mutex } *)

(** Builds the sequential dependency lemma between [descr] and [descr'] *)
let mk_depends_lemma
    table
    (system : Symbols.system)
    (descr : Action.descr) (descr' : Action.descr)
  : Goal.statement
  =
  assert (Action.depends
            (Action.get_shape_v descr.action)
            (Action.get_shape_v descr'.action));
  
  let sys_expr = SystemExpr.of_system table system in
  let a' = Term.mk_action descr'.name (Term.mk_vars descr'.indices) in
  let a =
    let indices =
      List.take (List.length descr.indices) descr'.indices
    in
    Term.mk_action descr.name (Term.mk_vars indices)
  in
  let tvar = Vars.make_fresh Type.ttimestamp "t" in
  let tau = Term.mk_var tvar in
  let form =
    Term.mk_forall ~simpl:false (tvar :: descr'.indices)
      (Term.mk_impls
         [Term.mk_happens tau;
          Term.mk_eq tau a' ]
         (Term.mk_lt a a'))
  in
  let name =
    Fmt.str "depends_%s_%s_%s"
      (Symbols.to_string system)
      (Symbols.to_string descr.name)
      (Symbols.to_string descr'.name)
  in
  Goal.{
    name;
    ty_vars = [];
    system = SystemExpr.reachability_context sys_expr;
    formula = Equiv.Local form;
  } 

(*------------------------------------------------------------------*)
(** Builds the mutual exlusivity lemma between [descr] and [descr'] *)
let mk_mutex_lemma
    table
    (system : Symbols.system)
    (descr : Action.descr) (descr' : Action.descr)
  : Goal.statement
  =
  let shape  = Action.get_shape_v  descr.action in
  let shape' = Action.get_shape_v descr'.action in
  assert (Action.mutex shape shape');

  let sys_expr = SystemExpr.of_system table system in

  (* number of common variables between mutually exclusives actions
     of [descr] and [descr'] *)
  let i_common = Action.mutex_common_vars shape shape' in
  
  let is_common, is_rem  = List.takedrop i_common  descr.indices in
  let _        , is_rem' = List.takedrop i_common descr'.indices in

  let a  = Term.mk_action descr.name  (Term.mk_vars (is_common @ is_rem))  in
  let a' = Term.mk_action descr'.name (Term.mk_vars (is_common @ is_rem')) in

  let form =
    Term.mk_forall ~simpl:false (is_common @ is_rem @ is_rem')
      (Term.mk_or
         (Term.mk_not (Term.mk_happens a))
         (Term.mk_not (Term.mk_happens a')))
  in
  let name =
    Fmt.str "mutex_%s_%s_%s"
      (Symbols.to_string system)
      (Symbols.to_string descr.name)
      (Symbols.to_string descr'.name)
  in
  Goal.{
    name;
    ty_vars = [];
    system = SystemExpr.reachability_context sys_expr;
    formula = Equiv.Local form;
  }

(*------------------------------------------------------------------*)
(** Compute the sequential dependencies and mutual exclusion lemmas 
    for a given system. *)
let mk_depends_mutex
    table (system : Symbols.system) : Goal.statement list
  =
  let descrs = System.descrs table system in
  System.Msh.fold (fun shape (descr : Action.descr) lems ->
      System.Msh.fold (fun shape' (descr' : Action.descr) lems ->
          if Action.depends shape shape' then
            mk_depends_lemma table system descr descr' :: lems
          else if Action.mutex shape shape' then
            mk_mutex_lemma table system descr descr' :: lems
          else lems
        ) descrs lems
    ) descrs []

let add_depends_mutex_lemmas table (system : Symbols.system) : Symbols.table =
  (* add axioms related to action dependancies *)
  let lems = mk_depends_mutex table system in
  Printer.pr "@[<v 0>Added action dependencies lemmas:@;@;";
  let table =
    List.fold_left (fun table lem ->
        add_lemma `Axiom lem table
      ) table lems
  in
  Printer.pr "@;@]";
  table
