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
    ("Template", Squirreltests.Template.tests);
    ("Include", Squirreltests.Main.includes);
    ("Tactics", Squirreltests.Main.tactics);
    ("Equivalence", Squirreltests.Main.equivalence);
    ("Channel", Squirreltests.Channel.channels);
    ("Models",         Squirreltests.Parserbuf.models);
    ("ProcessParsing", Squirreltests.Parserbuf.process_parsing);
    ("TermParsing",    Squirreltests.Parserbuf.term_parsing);
    ("Prover", Squirreltests.Prover.tests);
    ("Predicate", Squirreltests.Predicate.tests);
    ("Search", Squirreltests.Search.tests);
    ("NewTactics", Squirreltests.Tactics.tests);
    ("Term", Squirreltests.Term.tests);
    ("Projection", Squirreltests.Projection.tests)
  ]

let alcotests (runner:?test:bool -> string -> unit) (path:string) : (string * [> `Quick] * (unit -> unit )) list = 
  let exception Ok in
  let get_sp_from_dir s =
      Sys.readdir s
      |> Array.to_list
      |> List.filter (fun x -> Filename.extension x = ".sp")
      |> List.map (fun f -> Format.sprintf "%s/%s" s f) in

  let list_sp = get_sp_from_dir path in
  let okfails = List.map (fun f -> 
    f, `Quick, begin fun () -> Alcotest.check_raises "OK" Ok
      begin fun () ->
        (try runner ~test:true f
        with e -> begin
          Squirrelcore.Printer.prt `Error "%a"
            (Squirrelprover.Errors.pp_toplevel_error ~test:true
               (Squirrelprover.Driver.dummy_file ())) e;
            raise e
        end);
        raise Ok
      end
    end
    ) (list_sp) in
  okfails

let () =
  List.iter (fun (s,t) -> Squirrelcore.Checks.add_suite s t) test_suites;
  (* let runner = Squirrelprover.Prover.run in *)
  let runner = Squirrellib.Main.run in
  Squirrelcore.Checks.add_suite "tests/ok/" (alcotests runner "tests/ok");
  Squirrelcore.Checks.add_suite "tests/fail/" (alcotests runner "tests/fail");
  Format.eprintf "Running Alcotests on test suites :\n";
  List.iter (fun (n,_) -> 
    Format.eprintf "\t%s\n" n;
  ) (!Squirrelcore.Checks.suites);
  Format.eprintf "@.";

  Squirrelcore.Checks.run ()
