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
  let st = Prover.init ~with_prelude:true () in
  let st = Prover.exec_all ~test:true st 
      "\
type T.

op t : T.
op i : index.

op c1 : T -> bool.
op c2 : T -> bool.

namespace C1.
  op (+) : T -> T -> bool.
  op a = c1.
  name n : index -> message.
end C1.

(* same type signatures as in `C1` *)
namespace C2.
  op (+) : T -> T -> bool.
  op a = c2.
  name n : index -> message.
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
  let n : Term.term = term_of_string st1 "n i" in

  (* check that we pretty print the short paths [a t] and [n i] *)
  Alcotest.(check' string) ~msg:"short path: functions"
    ~actual:(Fmt.str "%a" (Term._pp ppe1) a)
    ~expected:"a t";

  Alcotest.(check' string) ~msg:"short path: names"
    ~actual:(Fmt.str "%a" (Term._pp ppe1) n)
    ~expected:"n i";

  (* in [st2], there is an ambiguity *)
  Alcotest.check_raises "ambiguity 1" Ok
    (fun () ->
       let _ : Term.term =
         try term_of_string st2 "a t" with
         | Squirrelcore.Theory.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );
  Alcotest.check_raises "ambiguity 2" Ok
    (fun () ->
       let _ : Term.term =
         try term_of_string st2 "n i" with
         | Squirrelcore.Theory.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );

  (* resolve the ambiguities  *)
  let a1 : Term.term = term_of_string st1 "C1.a t" in
  let a2 : Term.term = term_of_string st1 "C2.a t" in

  let n1 : Term.term = term_of_string st1 "C1.n i" in
  let n2 : Term.term = term_of_string st1 "C2.n i" in

  (* check that we **do not** pretty-print the short paths [a t] but rather
     and [C1.a t] (idem for the name [n]) *)
  Alcotest.(check' string) ~msg:"qualified paths 1"
    ~actual:(Fmt.str "%a" (Term._pp ppe2) a1)
    ~expected:"C1.a t";
  Alcotest.(check' string) ~msg:"qualified paths 2"
    ~actual:(Fmt.str "%a" (Term._pp ppe2) a2)
    ~expected:"C2.a t";

  Alcotest.(check' string) ~msg:"qualified paths 3"
    ~actual:(Fmt.str "%a" (Term._pp ppe2) n1)
    ~expected:"C1.n i";
  Alcotest.(check' string) ~msg:"qualified paths 4"
    ~actual:(Fmt.str "%a" (Term._pp ppe2) n2)
    ~expected:"C2.n i";

  ()

(*------------------------------------------------------------------*)
let crypto_parsing () =
  let exception Ok in
  let exception Ko in
  let st = Prover.init ~with_prelude:true () in

  let ill_formed_game st =
    Prover.exec_all ~test:true st 
      "\
game Foo = {
  oracle o (m: message) = {
    return m
  }

 oracle h = {
   return m 
  }
}.
"
  in
  Alcotest.check_raises "ill-formed game" Ok
    (fun () ->
       let _ : Prover.state =
         try ill_formed_game st with
         | Squirrelcore.Theory.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );

  ()

(*------------------------------------------------------------------*)
let tests = [
  ("typing"      , `Quick, Util.catch_error typing);
  ("game parsing", `Quick, Util.catch_error crypto_parsing);
]
