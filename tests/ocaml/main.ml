(** Various tests... *)

open Squirrelcore
module Prover = Squirrelprover.Prover
open Squirrellib.Main

let tactics =
  let exception Ok in
  let test = true in
  [
    "Name Finite 0", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/name-finite.sp" with
           | ProcessDecl.(Error (_,_,Failure "name can only be index by finite types")) -> raise Ok)
    end ;
    "Name Finite 2", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/name-finite2.sp" with
           | ProcessDecl.(Error (_,_,Failure "name can only be index by finite types")) -> raise Ok)
    end ;
    "Name Finite 3", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/name-finite3.sp" with
           | ProcessDecl.(Error (_,_,Failure "name can only be index by finite types")) -> raise Ok)
    end ;
    "Exists Intro", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/existsintro_fail.sp" with
           | Symbols.(Error (_, Unbound_identifier "a1")) -> raise Ok)
    end ;
    "TS not leq", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/ts_leq_not_lt.sp" with
           | Prover.Unfinished -> raise Ok)
    end ;
(* TODO: rework these tests.
   They were checking that the tactics failed as expected in cases
   where they were not supposed to apply. However, these tactics have been 
   generalised and now actually apply in these cases. *)
(*    "SEnc Bad SSC - INTCTXT 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/intctxt_nornd.sp" with
           | Tactics.Tactic_soft_failure (_,SEncNoRandom) -> raise Ok)
    end ;
    "SEnc Bad SSC - INTCTXT 2", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/intctxt_rndnotfresh.sp" with
           | Tactics.Tactic_soft_failure (_,SEncRandomNotFresh) -> raise Ok)
    end ;
    "Senc Bad SSC - INTCTXT 3", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/intctxt_sharedrnd.sp" with
           | Tactics.Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;
    "Senc Bad SSC - INTCTXT 4", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/intctxt_sharedrndind.sp" with
           | Tactics.Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;*)
   (* "Senc Bad SSC - CCA 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/cca_sharedrnd.sp" with
           | Tactics.Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;
    "Senc Bad SSC - CCA 2", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/cca_sharedrndframe.sp" with
           | Tactics.Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;
    "Senc Bad SSC - CCA 3", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/cca_nornd.sp" with
           | Tactics.Tactic_soft_failure (_,SEncNoRandom) -> raise Ok)
    end ;*)
    "Axiom Systems - 0", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/axiom2.sp" with
           | Tactics.Tactic_soft_failure (_,NoAssumpSystem _) -> raise Ok)
    end ;
    "Axiom Systems - 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/axiom3.sp" with
           | Symbols.Error (_, Symbols.Unbound_identifier "test") ->
             raise Ok)
    end ;
    "Substitution no capture", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/capture.sp" with
           | Prover.Unfinished -> raise Ok)
    end ;
    "Not Depends", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/depends.sp" with
           | Tactics.Tactic_soft_failure (_, Tactics.NotDepends _)
             -> raise Ok)
    end ;
    "Fresh Not Ground", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/fresh_reach_var.sp" with
           | Tactics.Tactic_soft_failure
               (_, Tactics.Failure "terms contain a non-constant variable: x") ->
             raise Ok)
    end ;
    "Check equalities false if unsupported terms", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/completion_unsupported_term.sp" with
           | Prover.Unfinished -> raise Ok)
    end ;
    "Indexed abstract", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/idx_abs.sp" with
           | Tactics.Tactic_soft_failure (_,Tactics.GoalNotClosed) -> raise Ok)
    end ;
    "Find equality", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/try.sp" with
           | Tactics.Tactic_soft_failure (_,CongrFail) -> raise Ok)
    end ;
    "Undo does not maintain old truth", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/undo.sp" with
           | Prover.Unfinished -> raise Ok)
    end ;
    "Undo out of proof does not assert false", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/undo_proof.sp" with
           (* parser.interactive does not accept Qed anymore *)
           | Squirrelfront.Parser.Error -> raise Ok)
    end 
  ] 

(*------------------------------------------------------------------*)
let equivalence =
  let exception Ok in
  let test = true in
  [
    "Fresh Frame", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/fresh_frame.sp" with
           | Prover.Unfinished -> raise Ok)
    end ;
    "Fresh System", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/fresh_system.sp" with
           | Tactics.Tactic_soft_failure (_,Tactics.GoalNotClosed) ->
             raise Ok)
    end ;
    "DDH", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/ddh.sp" with
           | Tactics.Tactic_soft_failure (_,Tactics.NotDDHContext) -> raise Ok)
    end ;

    "FA Dup Input", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/fadup_input.sp" with
           | Tactics.Tactic_soft_failure (_,Tactics.NoReflMacroVar) -> raise Ok)
    end ;
    "XOR2", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/xor2.sp" with
           | Tactics.Tactic_soft_failure
               (_, Failure "name is not XORed on both sides") ->
             raise Ok)
    end ;
    "Not XOR", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/notxor.sp" with
           | Tactics.Tactic_soft_failure
               (_, Failure "Xor can only be applied on a term with at least one \
                            occurrence of a term xor(t,k)")  ->
             raise Ok)
    end ;
    "Pred Init", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/pred.sp" with
           | Prover.Unfinished -> raise Ok)
    end ;
    "DDH not PQ Sound", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/pqsound.sp" with
           | Tactics.Tactic_hard_failure (_,Tactics.TacticNotPQSound) -> raise Ok)
    end
  ]

(*------------------------------------------------------------------*)
let includes =
    let exception Ok in
    let test = true in
    [
    "Cycle", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/IncludeCycle.sp" with
           | Command.Cmd_error (IncludeCycle _) -> raise Ok)
    end ;
    "Theory not found", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/include-unknown.sp" with
           | Command.Cmd_error (IncludeNotFound _) -> raise Ok)
    end ;
    (* Not that in test mode, errors during an include are not wrapped
       into a IncludeError.  *)
    "Re-define", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/include-rebind.sp" with
           | Symbols.(Error (_, Multiple_declarations _)) ->
             raise Ok)
    end ;
    "Re-define", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/include-rebind2.sp" with
           | Symbols.(Error (_, Multiple_declarations _)) ->
             raise Ok)
    end ;
    "Undefined Action", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/bad-actions.sp" with
             Theory.Conv (_, UndefInSystem _) -> raise Ok)
    end ;
  ]
