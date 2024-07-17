(** Main executable for running Alcotest unit tests. *)

(* These modules register tests suites as side effects,
 * and must be forcibly loaded. These tests may be hard to
 * extract from the modules as they may rely on abstract types. *)
open! Squirrelcore.Constr
open! Squirrelcore.Completion
open! Squirrelcore.Tactics
open! Squirrelcore.Term
open! Squirrelcore.Theory
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
        Squirrelcore.Printer.prt `Error "%a"
          (Squirrelprover.Errors.pp_toplevel_error
             ~test:true
             Squirrelprover.Driver.dummy)
          e;
        raise e
    end
  in
  List.map make_test list_sp

let () =
  List.iter (fun (s,t) -> Squirrelcore.Checks.add_suite s t) test_suites;
  (* let runner = Squirrelprover.Prover.run in *)
  let runner = Squirrellib.Main.run in
  Squirrelcore.Checks.add_suite "tests/ok/" (alcotests runner "tests/ok");
  Format.eprintf "Running Alcotests on test suites :\n";
  List.iter (fun (n,_) -> 
    Format.eprintf "\t%s\n" n;
  ) (!Squirrelcore.Checks.suites);
  Format.eprintf "@.";

  Squirrelcore.Checks.run ()
