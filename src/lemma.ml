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

let as_lemma : Symbols.data -> lemma = function
  | Lemma s -> s
  | _ -> assert false
 
(*------------------------------------------------------------------*)
let find gname table : Goal.statement =
  let lem = as_lemma (Symbols.Lemma.data_of_lsymb gname table) in
  lem.stmt

let find_opt gname table : Goal.statement option =
  if not (Symbols.Lemma.mem gname table)
  then None
  else Some (find gname table)

(*------------------------------------------------------------------*)
let mem gname table : bool =
  Symbols.Lemma.mem gname table

let mem_reach gname table : bool =
  match find_opt gname table with
  | None -> false
  | Some s -> Goal.is_reach_statement s

let mem_equiv gname table : bool =
  match find_opt gname table with
  | None -> false
  | Some s -> Goal.is_equiv_statement s

(*------------------------------------------------------------------*)
let find_reach gname table =
  Goal.to_reach_statement ~loc:(L.loc gname) (find gname table)

let find_equiv gname table =
  Goal.to_equiv_statement ~loc:(L.loc gname) (find gname table)

(*------------------------------------------------------------------*)
let find_kind gname table : [`Axiom | `Lemma] =
  let lem = as_lemma (Symbols.Lemma.data_of_lsymb gname table) in
  lem.kind

(*------------------------------------------------------------------*)
let add_lemma
    ?(loc = L._dummy)
    (kind : [`Axiom | `Lemma]) (gconcl : Goal.statement)
    (table : Symbols.table) : Symbols.table
  =
  let data = Lemma { stmt = gconcl; kind } in
  let table, _ =
    Symbols.Lemma.declare_exact table (L.mk_loc loc gconcl.Goal.name) ~data ()
  in
  table

(*------------------------------------------------------------------*)
let print_all fmt table : unit =
  Symbols.Lemma.iter (fun _ _ data ->
      let g = as_lemma data in
      Fmt.pf fmt "%s: %a@;" g.stmt.name Equiv.Any.pp g.stmt.formula
    ) table

