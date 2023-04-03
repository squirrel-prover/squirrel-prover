(** Main executable for running Alcotest unit tests. *)

(* These modules register tests suites as side effects,
 * and must be forcibly loaded. These tests may be hard to
 * extract from the modules as they may rely on abstract types. *)
open! Squirrellib.Constr
open! Squirrellib.Completion
open! Squirrellib.Tactics
open! Squirrellib.Term
open! Squirrellib.Theory
open! Squirrellib.Vars

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
    ("Search", Squirreltests.Search.tests);
    ("NewTactics", Squirreltests.Tactics.tests);
    ("Term", Squirreltests.Term.tests)
  ]

let alcotests (path:string) : (string * [> `Quick] * (unit -> unit )) list = 
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
        Squirrellib.Main.run ~test:true f;
        raise Ok
      end
    end
    ) (list_sp) in
  okfails

let () =
  List.iter (fun (s,t) -> Squirrellib.Checks.add_suite s t) test_suites;
  Squirrellib.Checks.add_suite "tests/ok/" (alcotests "tests/ok");
  Squirrellib.Checks.add_suite "tests/fail/" (alcotests "tests/fail");
  Format.eprintf "Running Alcotests on test suites :\n";
  List.iter (fun (n,_) -> 
    Format.eprintf "\t%s\n" n;
  ) (!Squirrellib.Checks.suites);
  Format.eprintf "@.";

  Squirrellib.Checks.run ()
