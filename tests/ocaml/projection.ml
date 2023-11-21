open Squirrelcore
open Squirrelfront
open Squirrelprover

let term : Term.term Alcotest.testable =
   Alcotest.testable Term.pp_dbg Term.equal

let any_form : Equiv.any_form Alcotest.testable =
  Alcotest.testable Equiv.Any.pp_dbg Equiv.Any.equal

let get_hyp sequent name =
  snd (TraceSequent.Hyps.by_name_k (Location.(mk_loc _dummy) name) Hyp sequent) 

(* Utility to parse formulas from strings. *)
let formula_of_string st string : Equiv.local_form =
  let th_tm = Util.parse_from_string Parser.top_formula string in
  let env = Env.init ~table:(Prover.get_table st) () in
  let tm,ty =
    Theory.convert Theory.{ env ; cntxt = InGoal } th_tm in
  assert (ty = Boolean);
  tm

let tests =
  [
    "project [phi]", `Quick, begin fun () ->
      let st =
        Prover.exec_all ~test:true (Prover.init ())
          "system null.\n\
           abstract p : bool.\n\
           abstract q : bool.\n\
           global lemma _ : [diff(p,q)] -> [diff(p,q) => false].\n\
           Proof.\n\
           intro Hglob. intro Hloc.\n\
           project."
      in
      let subgoals = Prover.get_subgoals st in
      assert (List.length subgoals = 2);
      match List.hd subgoals with
      | Goal.Global _ -> assert false
      | Goal.Local s ->
          Alcotest.check any_form
            "global hypothesis should be projected"
            (Global (Atom (Reach (formula_of_string st "p"))))
            (get_hyp s "Hglob");
          Alcotest.check any_form
            "local hypothesis should be projected"
            (Local (formula_of_string st "p"))
            (get_hyp s "Hloc")
    end ;
  ]
