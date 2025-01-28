(** Main executable for running Alcotest unit tests. *)

(* These modules register tests suites as side effects,
 * and must be forcibly loaded. These tests may be hard to
 * extract from the modules as they may rely on abstract types. *)
open! Squirrelcore.Constr
open! Squirrelcore.Completion
open! Squirrelcore.Tactics
open! Squirrelcore.Term
open! Squirrelcore.Typing
open! Squirrelcore.Vars

let test_suites : unit Alcotest.test list =
  [
    ("Template"       , Squirreltests.Template.tests);
    ("Include"        , Squirreltests.Main.includes);
    ("Tactics"        , Squirreltests.Main.tactics);
    ("Equivalence"    , Squirreltests.Main.equivalence);
    ("Channel"        , Squirreltests.Channel.channels);
    ("Models"         , Squirreltests.Parserbuf.models);
    ("ProcessParsing" , Squirreltests.Parserbuf.process_parsing);
    ("TermParsing"    , Squirreltests.Parserbuf.term_parsing);
    ("Prover"         , Squirreltests.Prover.tests);
    ("Predicate"      , Squirreltests.Predicate.tests);
    ("Search"         , Squirreltests.Search.tests);
    ("NewTactics"     , Squirreltests.Tactics.tests);
    ("Term"           , Squirreltests.Term.tests);
    ("Projection"     , Squirreltests.Projection.tests);
    ("Typing"         , Squirreltests.Typing.tests);
  ]

let alcotests (runner:?test:bool -> string -> unit) (path:string) : (string * [> `Quick] * (unit -> unit )) list = 
  let list_sp =
    Sys.readdir path
    |> Array.to_list
    |> List.filter (fun x -> Filename.extension x = ".sp")
    |> List.map (fun f -> Filename.concat path f)
  in
  let make_test filename =
    filename, `Quick, begin fun () ->
      try runner ~test:true filename with e ->
        let table = Squirrelcore.Symbols.builtins_table () in
        Squirrelcore.Printer.prt `Error "%a"
          (Squirrelprover.Errors.pp_toplevel_error
             ~test:true
             Squirrelprover.Driver.dummy table)
          e;
        raise e
    end
  in
  List.map make_test list_sp

let () =
  List.iter (fun (s,t) -> Squirrelcore.Checks.add_suite s t) test_suites;
  let runner = Squirrellib.Main.run in
  begin match Smt.files () with 
    | None -> ()
    | Some folder -> 
      Squirrelcore.Checks.add_suite folder (alcotests runner folder);
  end;
  Squirrelcore.Checks.add_suite "tests/ok/" (alcotests runner "tests/ok");
  Squirrelcore.Checks.run ()
