(** Test the typer and pretty-printer *)

(*------------------------------------------------------------------*)
open Squirrelcore
open Squirrelfront
module ProverLib = ProverLib

module Prover = Squirrelprover.Prover


open Util

(*------------------------------------------------------------------*)
(** utility to parse a term from a string. *)
let term_of_string st string : Term.term =
  let t_p = Util.parse_from_string Parser.top_formula string in
  let env = Env.init ~table:(Prover.get_table st) () in
  let t,_ = Theory.convert Theory.{ env ; cntxt = InGoal } t_p in
  t

(*------------------------------------------------------------------*)
let typing () =
  let exception Ok in
  let exception Ko in
  let st = Prover.init ~with_prelude:false () in
  let st = Prover.exec_all ~test:true st 
      "\
type T.

op t : T.

op c1 : T -> bool.
op c2 : T -> bool.

namespace C1.
  op (+) : T -> T -> bool.
  op a = c1.
end C1.

(* same type signatures as in `C1` *)
namespace C2.
  op (+) : T -> T -> bool.
  op a = c2.
end C2.
"
  in
  (* first, open only [C1] *)
  let st1 = Prover.exec_all ~test:true st "open C1." in
  (* open [C2], now there is an ambiguity between [C1.a] and [C2.a] 
     (idem [C1.(+)] and [C2.(+)]) *) 
  let st2 = Prover.exec_all ~test:true st1 "open C2." in

  let ppe1 = Ppenv.default_ppe ~dbg:false ~table:(Prover.get_table st1) () in
  let ppe2 = Ppenv.default_ppe ~dbg:false ~table:(Prover.get_table st2) () in
    
  (* in [st1], no ambiguities *)
  let a : Term.term = term_of_string st1 "a t" in
  (* check that we pretty print the short name [a t] *)
  Alcotest.(check' string) ~msg:"short names"
    ~actual:(Fmt.str "%a" (Term._pp ppe1) a)
    ~expected:"a t";

  (* in [st2], there is an ambiguity *)
  Alcotest.check_raises "TODO" Ok
    (fun () ->
       let _ : Term.term =
         try term_of_string st2 "a t" with
         | Squirrelcore.Theory.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );


  (* resolve the ambiguities  *)
  let a1 : Term.term = term_of_string st1 "C1.a t" in
  let a2 : Term.term = term_of_string st1 "C2.a t" in
  (* check that we **do not** pretty-print the short names [a t] by rather
     and [C1.a t] *)
  Alcotest.(check' string) ~msg:"qualified names"
    ~actual:(Fmt.str "%a" (Term._pp ppe2) a1)
    ~expected:"C1.a t";
  Alcotest.(check' string) ~msg:"qualified names"
    ~actual:(Fmt.str "%a" (Term._pp ppe2) a2)
    ~expected:"C2.a t";

  ()

(*------------------------------------------------------------------*)
let tests = [ ("typing", `Quick, Util.catch_error typing); ]
