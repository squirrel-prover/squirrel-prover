open Utils
open Ppenv

module L  = Location
module SE = SystemExpr
               
(*------------------------------------------------------------------*)
(** A top-level axiom or proved lemma. *)

type lemma = { 
  stmt : Goal.statement;
  kind : [`Axiom | `Lemma];
} 

type Symbols.data += Lemma of lemma

(*------------------------------------------------------------------*)
let pp_kind fmt = function
  | `Axiom -> Printer.kw `Goal fmt "axiom"
  | `Lemma -> Printer.kw `Goal fmt "lemma"

let _pp ppe fmt lem =
  let stmt_kind_str =
    match lem.stmt.formula with
    | Equiv.GlobalS _ -> "global "
    | Equiv.LocalS  _ -> ""
  in
  Fmt.pf fmt "@[<hov 2>%s%a %a@]"
    stmt_kind_str
    pp_kind lem.kind (Goal._pp_statement ppe) lem.stmt

let pp_dbg = _pp (default_ppe ~dbg:true  ())
let pp     = _pp (default_ppe ~dbg:false ())

(*------------------------------------------------------------------*)
let as_lemma : Symbols.data -> lemma = function
  | Lemma s -> s
  | _ -> assert false

(*------------------------------------------------------------------*)
(** error message: many lemma with a given type *)
let failure_cannot_desambiguate 
    loc table (lemmas : (Symbols.lemma * lemma) list) 
  =
  let ppe = default_ppe ~table () in
  let err = 
    Fmt.str "could not desambiguate between lemmas:@;<1 2>@[<v 0>%a@]"  
      (Fmt.list ~sep:(Fmt.any "@;@;")
         (fun fmt (_path, lemma) ->
            Fmt.pf fmt "%a" (_pp ppe) lemma
         )
      ) lemmas
  in
  Typing.error loc (Failure err) 

(*------------------------------------------------------------------*)
let find (path : Symbols.p_path) table : lemma =
  let lemmas = 
    Symbols.Lemma.convert path table |>
    List.map (snd_bind as_lemma)
  in

  if List.length lemmas > 1 then
    failure_cannot_desambiguate (Symbols.p_path_loc path) table lemmas;

  as_lemma (snd (Symbols.Lemma.convert1 path table))

let find_opt path table : lemma option =
  if Symbols.Lemma.mem_p path table
  then Some (find path table)
  else None

(*------------------------------------------------------------------*)
let find_stmt_local path table =
  Goal.to_local_statement ~loc:(Symbols.p_path_loc path ) (find path table).stmt

let find_stmt_global path table =
  Goal.to_global_statement ~loc:(Symbols.p_path_loc path) (find path table).stmt

(*------------------------------------------------------------------*)
let find_stmt path table : Goal.statement    = (find path table).stmt
let find_kind path table : [`Axiom | `Lemma] = (find path table).kind

(*------------------------------------------------------------------*)
let mem path table : bool = Symbols.Lemma.mem_p path table

let mem_local gname table : bool =
  match find_opt gname table with
  | None -> false
  | Some s -> Goal.is_local_statement s.stmt

let mem_global gname table : bool =
  match find_opt gname table with
  | None -> false
  | Some s -> Goal.is_global_statement s.stmt

(*------------------------------------------------------------------*)
let add_lemma
    ?(loc = L._dummy)
    (kind : [`Axiom | `Lemma]) (gconcl : Goal.statement)
    (table : Symbols.table) : Symbols.table
  =
  let lem = { stmt = gconcl; kind } in
  let data = Lemma lem in
  let table, _ =
    Symbols.Lemma.declare ~approx:false table (L.mk_loc loc gconcl.Goal.name) ~data 
  in
  let ppe = default_ppe ~table () in
  Printer.pr "%a@;" (_pp ppe) lem;
  table

(*------------------------------------------------------------------*)
let print_all fmt table : unit =
  let ppe = default_ppe ~table () in
  Symbols.Lemma.iter (fun _ data ->
      let g = as_lemma data in
      Fmt.pf fmt "%s: %a@;" 
        g.stmt.name
        (Equiv.Any_statement._pp ppe) g.stmt.formula
    ) table


(*------------------------------------------------------------------*)
(** {2 Dependency and mutual exclusion (conflict) axioms} *)

(** Build the sequential dependency lemma between [descr] and [descr']. *)
let mk_depends_lemma
    (s : Symbols.system) (descr : Action.descr) (descr' : Action.descr)
  : Goal.statement
  =
  assert (Action.depends
            (Action.get_shape_v descr.action)
            (Action.get_shape_v descr'.action));
  
  let a' = Term.mk_action descr'.name (Term.mk_vars descr'.indices) in
  let a =
    let indices =
      List.take (List.length descr.indices) descr'.indices
    in
    Term.mk_action descr.name (Term.mk_vars indices)
  in
  let form =
    Term.mk_forall ~simpl:false descr'.indices
      (Term.mk_impls
         [Term.mk_happens a']
         (Term.mk_lt a a'))
  in
  let name =
    Fmt.str "depends_%s_%s"
      (Symbols.path_to_string descr.name)
      (Symbols.path_to_string descr'.name)
  in
  let v = SE.Var.of_ident (Ident.create "'P") in
  Goal.{
    name;
    params  = { Params.empty with se_vars = [v,[SE.Var.Compatible_with s]]; };
    system  = { set = SE.var v; pair = None; };
    formula = Equiv.LocalS {formula = form; bound = None};
  } 
  (* TODO: Concrete: put a `0` bound instead *)

(*------------------------------------------------------------------*)
(** Build the mutual exlusivity lemma between [descr] and [descr']. *)
let mk_mutex_lemma
    (s : Symbols.system) (descr : Action.descr) (descr' : Action.descr)
  : Goal.statement
  =
  let shape  = Action.get_shape_v  descr.action in
  let shape' = Action.get_shape_v descr'.action in
  assert (Action.mutex shape shape');

  (* number of common variables between mutually exclusives actions
     of [descr] and [descr'] *)
  let i_common = Action.mutex_common_vars shape shape' in
  
  let is_common, is_rem  = List.takedrop i_common  descr.indices in
  let _        , is_rem' = List.takedrop i_common descr'.indices in

  let a  = Term.mk_action descr.name  (Term.mk_vars (is_common @ is_rem))  in
  let a' = Term.mk_action descr'.name (Term.mk_vars (is_common @ is_rem')) in

  let formula =
    Term.mk_forall ~simpl:false (is_common @ is_rem @ is_rem')
      (Term.mk_or
         (Term.mk_not (Term.mk_happens a))
         (Term.mk_not (Term.mk_happens a')))
  in
  let name =
    Fmt.str "mutex_%s_%s"
      (Symbols.path_to_string descr.name)
      (Symbols.path_to_string descr'.name)
  in
  let v = SE.Var.of_ident (Ident.create "'P") in
  Goal.{
    name;
    params  = { Params.empty with se_vars = [v,[SE.Var.Compatible_with s]]; };
    system  = { set = SE.var v; pair = None; };
    formula = Equiv.LocalS {formula; bound = None};
  }
  (* TODO: Concrete: put a `0` bound instead *)

(*------------------------------------------------------------------*)
(** Compute the sequential dependency and mutual exclusion lemmas
    for a given system. *)
let mk_depends_mutex
    table (system : Symbols.system) : Goal.statement list
  =
  let descrs = System.descrs table system in
  System.Msh.fold (fun shape (descr : Action.descr) lems ->
      System.Msh.fold (fun shape' (descr' : Action.descr) lems ->
          if Action.depends shape shape' then
            mk_depends_lemma system descr descr' :: lems
          else if Action.mutex shape shape' then
            mk_mutex_lemma system descr descr' :: lems
          else lems
        ) descrs lems
    ) descrs []

(** Generate the sequential dependency and mutual exclusion lemmas
    for a given system, and add them to the table. *)
let add_depends_mutex_lemmas table (system : Symbols.system) : Symbols.table =
  (* add axioms related to action dependancies *)
  let lems = mk_depends_mutex table system in
  Printer.pr "@[<v 0>Added action dependencies lemmas:@;@;";
  let table =
    List.fold_left
      (fun table lem ->
         (* Try to add_lemma. This can fail if actions from a previous
            system have been re-used; in that case the dependency lemma
            has been added for the first system so we simply skip it. *)
         try add_lemma `Axiom lem table with
         | Symbols.Error (_, Multiple_declarations _) -> table)
      table lems
  in
  Printer.pr "@;@]";
  table
