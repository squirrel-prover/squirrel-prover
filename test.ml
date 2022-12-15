(* NOTE: somehow these "open!" are necessary to perform the side effects
 *       in each opened module; we use "open!" instead of "open" to avoid
 *       an "unused open" warning *)

open! Squirrellib.Channel
open! Squirrellib.Process
open! Squirrellib.Term
open! Squirrellib.Constr
open! Squirrellib.Lexer
open! Squirrellib.Completion
open! Squirrellib.Parserbuf
open! Squirrellib.Main


(* module ToplevelProver = *)
(*   Squirrellib.TopLevel.Toplevel(Squirrellib.Prover) *)

module P = Squirrellib.Prover
module L = Squirrellib.Location
module D = Squirrellib.Decl
module T = Squirrellib.Theory
module C = Squirrellib.TConfig
module Co = Squirrellib.Config
module Pl = Squirrellib.ProverLib

module Lexer = Squirrellib.Lexer


let alcotests (path:string) : (string * [> `Quick] * (unit -> unit )) list = 
  let exception Ok in

  let get_sp_from_dir s =
      Sys.readdir s
      |> Array.to_list
      |> List.filter (fun x -> Filename.extension x = ".sp")
      |> List.map (fun f -> Format.sprintf "%s/%s" s f) in

  let list_sp = get_sp_from_dir path in
  (* List.iter (fun x -> Format.printf "%s\n" x) list_sp_ok; *)

  let okfails = List.map (fun f -> 
    Filename.basename f, `Quick, begin fun () -> Alcotest.check_raises "OK" Ok
      begin fun () ->
        let _ = try Squirrellib.Main.run ~test:true f with 
          | e -> raise e in
        raise Ok
      end
    end
    ) (list_sp) in
  okfails

let () =
  Squirrellib.Checks.add_suite "OK" (alcotests "tests/ok");
  Squirrellib.Checks.add_suite "FAILS" (alcotests "tests/fail");
  Format.eprintf "Running Alcotests from :\n";
  List.iter (fun (n,_) -> 
    Format.eprintf "%s\n" n;
  ) (!Squirrellib.Checks.suites);

  Squirrellib.Checks.run ()
