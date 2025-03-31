(** Utilities for testing. *)

open Squirrelcore
open Squirrelfront

module Prover = Squirrelprover.Prover
module Typing = Squirrelcore.Typing

let catch_error (f:unit -> unit) () : unit  =
  try 
    f ();()
  with e ->
    let table = Symbols.builtins_table () in
    Squirrelcore.Printer.prt `Error "%a"
      (Squirrelprover.Errors.pp_toplevel_error ~test:true 
         Squirrelprover.Driver.dummy table) e;
    raise e

let parse_from_string 
    (parse_fun : (Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a)
    (s:string) 
  : 'a
  =
  let lexbuf = Sedlexing.Utf8.from_string s in
  let lexer = Sedlexing.with_tokenizer Sedlexer.token lexbuf in
  let parse_fun = MenhirLib.Convert.Simplified.traditional2revised parse_fun in
  parse_fun lexer

let term_from_string (s:string) =
  let t = parse_from_string Parser.top_formula s in
  Typing.Local t

let global_formula_from_string (s:string) =
  let t = parse_from_string Parser.top_global_formula s in
  Typing.Global t

(* FIXME: Menhir bug (see parser.mly
   preventing us from exporting the system expression parser as a
   top-level construct. *)
(* let sexpr_from_string (s:string) = *)
(*   parse_from_string Parser.system_expr s  *)

let find_in_sys_from_string s st =
  let env = 
    begin match Prover.get_mode st with
    | ProofMode -> 
      let goal = match Prover.get_current_goal st with
        | None -> assert false
        | Some (ProofObl g)
        | Some (UnprovedLemma (_, g)) -> g
      in
      begin match goal with
        | Goal.Local  j -> LowTraceSequent.env j
        | Goal.Global j -> LowEquivSequent.env j
      end
    | _ -> assert false
    end
  in
  let x = match term_from_string s with 
    | Typing.Local x -> x
    | _ -> assert false
  in
  let cntxt = Typing.{ env; cntxt = InGoal; } in
  let x,_ = Typing.convert cntxt x in
  x
