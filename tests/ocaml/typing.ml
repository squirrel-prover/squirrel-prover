(** Test the typer and pretty-printer *)

(*------------------------------------------------------------------*)
open Squirrelcore
open Squirrelfront
module ProverLib = ProverLib

module Prover = Squirrelprover.Prover
module Typing = Squirrelcore.Typing

open Util

(*------------------------------------------------------------------*)
exception Ok 
exception Ko
  
(*------------------------------------------------------------------*)
(** utility to parse a term from a string. *)
let term_of_string st string : Term.term =
  let t_p = Util.parse_from_string Parser.top_formula string in
  let env = Env.init ~table:(Prover.get_table st) () in
  let t,_ = Typing.convert Typing.{ env ; cntxt = InGoal } t_p in
  t

(*------------------------------------------------------------------*)
let reify () =
  let st = Prover.init () in
  let st = Prover.exec_all ~test:true st
      "\
include Reify.

type T.
op f : T -> bool.

system null.
channel c.
process A = out(c,witness).
system toto = A.

op phi : bool -> bool.
op psi ['a] : 'a -> bool.
op p : bool.
op m : message.
op t_ : T.
op s : string.
op i : int.
name n : bool.
"
  in
  let st_namespace = Prover.exec_all ~test:true st
      "
      namespace Test.
      namespace Testing.
      type t.
      op tt : t.
     "
  in
  let st_post1 = Prover.exec_all ~test:true st_namespace
      "
       end Testing.
       end Test.
       senc enc,dec.
      "
  in
  let st_post2 = Prover.exec_all ~test:true st_namespace
      "
       end Testing.
       end Test.

       open Test.
      "
  in

  let quoting (t : string) (st : Prover.state) : Term.term =
    term_of_string st ("|\"" ^ t ^ "\"|")
  in
  let print_out (t : string) = "{\"" ^ t ^ "\"}" in

  let ppe (st : Prover.state) =
    Ppenv.default_ppe ~dbg:false ~table:(Prover.get_table st) ()
  in
  (*
This function test that the reification of t (in the prover state st) is pretty-printted as :
- {"s"} when o = Some s
- {"t"} when o = None
*)
  let testing ((t,o,st) : string*string option*Prover.state) =
    let o = Utils.oget_dflt t o in
    Alcotest.(check' string) ~msg:("reification error on term" ^ t)
      ~actual:(Fmt.str "%a" (Term._pp (ppe st)) (quoting t st))
      ~expected:(print_out o);
  in
  List.iter testing [
    ("s",None,st);
    ("3",None,st);
    ("i",None,st);
    ("m",None,st);
    ("n",None,st);
    ("phi",None,st);
    ("psi[bool]",Some "psi",st);
    ("psi[int*int]",Some "psi",st);
    ("psi[T]",Some "psi",st);
    ("psi s",None,st);
    ("|\"phi true\"|",Some "{\"phi true\"}",st);
    ("forall x, phi x",Some "forall (x:bool), phi x",st);
    ("forall (x:bool), psi x",None,st);
    ("fun x => (phi x, x)",Some "fun (x:bool) => (phi x, x)",st);
      ("let x = psi true in psi x",None,st);
    ("try find x such that phi x in psi x else true",
     Some "try find x:bool such that phi x in psi x else true",st);
    ("try find (x:bool) such that phi x in psi x else true",
     Some "try find x:bool such that phi x in psi x else true",st);
    ("tt",None,st_namespace);
    ("psi tt",None,st_namespace);
    ("Test.Testing.tt",None,st_post1);
    ("psi Test.Testing.tt",None,st_post1);
    ("Testing.tt",Some "Test.Testing.tt",st_post2);
    ("psi Testing.tt",Some "psi Test.Testing.tt",st_post2);
    ("enc",None,st_post1)
  ]


(*------------------------------------------------------------------*)
(*------------------------------------------------------------------*)
let namespaces () =
  let st = Prover.init () in
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
         | Squirrelcore.Typing.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );
  Alcotest.check_raises "ambiguity 2" Ok
    (fun () ->
       let _ : Term.term =
         try term_of_string st2 "n i" with
         | Squirrelcore.Typing.Error (_, Failure _) -> raise Ok
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

  let ill_formed_game () =
    let st = Prover.init () in
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
         try ill_formed_game () with
         | Squirrelcore.Typing.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );

  (*------------------------------------------------------------------*)
  (* check that games cannot use names or macros *)
  begin
    let init =
      Prover.exec_all ~test:true (Prover.init ()) "name k : message." 
    in
    let g0 = "\
game G = {
  var x = empty;
  oracle g = { 
    x := input@init;
    return empty;
  }
}."
    in
    let g1 = "\
game G = {
  var x = empty;
  oracle g = { 
    x := k;
    return empty;
  }
}."
    in
    let g2 = "\
game G = {
  oracle g = { 
    var x : message = input@init;
    return empty;
  }
}."
    in
    let g3 = "\
game G = {
  oracle g = { 
    var x : message = k;
    return empty;
  }
}."
    in
    let g4 = "\
game G = {
  oracle g = { return input@init; }
}."
    in
    let g5 = "\
game G = {
  oracle g = { return k; }
}."
    in
    let g6 = "\
game G = {
  var x : message = input@init;
}."
    in
    let g7 = "\
game G = {
  var x : message = k;
}."
    in
    let check_typing_error (g : string) =
      Alcotest.check_raises "ill-formed game" Ok
        (fun () ->
           let _ : Prover.state =
             try Prover.exec_all ~test:true init g with
             | Squirrelcore.Typing.Error (_, Failure _) -> raise Ok
           in
           raise Ko
        );
    in
    List.iter check_typing_error [g0;g1;g2;g3;g4;g5;g6;g7]
  end;
  
  ()

(*------------------------------------------------------------------*)
let type_arguments () =
  let st = Prover.init () in
  let st = Prover.exec_all ~test:true st 
      "\
type T.
op foo ['a] : 'a.
op bar ['a 'b] : ('a * 'b).
"
  in
  (* positive tests *)
  let _ : Term.term = term_of_string st "foo[message] = empty" in
  let _ : Term.term = term_of_string st "bar[message,bool]    = (empty,true)" in
  let _ : Term.term = term_of_string st "bar[message,message] = (empty,empty)" in
  let _ : Term.term = term_of_string st "bar[message,bool]    = witness" in

  (* negative tests *)
  Alcotest.check_raises "type argument 1" Ok
    (fun () ->
       let _ : Term.term =
         try term_of_string st "foo[bool] = empty" with
         | Squirrelcore.Typing.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );
  Alcotest.check_raises "type argument 2" Ok
    (fun () ->
       let _ : Term.term =
         try term_of_string st "bar[message,message] = (empty,true)" with
         | Squirrelcore.Typing.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );
  Alcotest.check_raises "type argument 3" Ok
    (fun () ->
       let _ : Term.term =
         try term_of_string st "bar[message,message] = (true,empty)" with
         | Squirrelcore.Typing.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );
  Alcotest.check_raises "too many type arguments" Ok
    (fun () ->
       let _ : Term.term =
         try term_of_string st "bar[message,message,message]" with
         | Squirrelcore.Typing.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );

  ()
  
(*------------------------------------------------------------------*)
let let_def () =
  let init = Prover.init () in

  let let_def_type_error st s = 
    try ignore (Prover.exec_all ~test:true st s : Prover.state); false with
    | Squirrelcore.Typing.Error (_, _) -> true
  in

  let st = 
    Prover.exec_all ~test:true init "\
channel c.
system P = !_i in(c,x); A: out(c,x); !_j B:out(c,x) | D: out(c,empty).
system Q = !_i in(c,x); A: out(c,x).\
"
  in

  Alcotest.(check' bool) ~msg:"unknown action in system" 
    ~expected:true
    ~actual:(let_def_type_error st "\
let gfailed @like:Q (x : int) t with
| B (_,_) -> 1.
");

  Alcotest.(check' bool) ~msg:"unknown action in system2" 
    ~expected:true
    ~actual:(let_def_type_error st "\
let gfailed2 @like:Q (x : int) t with
| D -> 1.
");

  Alcotest.(check' bool) ~msg:"unknown action in system" 
    ~expected:true
    ~actual:(let_def_type_error st "\
let gfailed @like:Q (x : int) t with
| B (_,_) -> 1.
");

  (*------------------------------------------------------------------*)

  (* positive exhaustiveness checks *)
  let _ : Prover.state = 
    Prover.exec_all ~test:true init "\
let bool_to_int (x : bool) with
| true  -> 1
| false -> 0.
"
  in
  let _ : Prover.state = 
    Prover.exec_all ~test:true init "\
let test1 (x : bool * bool) with
| (true , _) -> 1
| (false, _) -> 0.
"
  in
  let _ : Prover.state = 
    Prover.exec_all ~test:true init "\
let test2 (x : bool * bool) with
| (true , _) -> 1
| (false, false) -> 0
| (false, true ) -> 2.
"
  in

  (*------------------------------------------------------------------*)
  let stP = 
    Prover.exec_all ~test:true (Prover.init ()) "\
channel c.
system P = !_i in(c,x); A: out(c,empty).
op prop : bool.
" 
  in

  (* should succeed *)
  let _ = 
    Prover.exec_all ~test:true stP "\
let f @system:P (x : int) u with
| A i     when happens (A i)     -> 0
| init                           -> 1
| _       when not (happens u)   -> 2.
"
  in

  ()


(*------------------------------------------------------------------*)
let generic_typing () =
  let st = Prover.init () in
  let st = Prover.exec_all ~test:true st 
      "\
type E[enum].
type T.
"
  in
  (* positive tests *)
  let _ : Term.term = term_of_string st "seq(i : E => i)" in
  let _ : Term.term = term_of_string st "seq(i : index => i)" in
  let _ : Term.term = term_of_string st "seq(i : timestamp => i)" in

  (* negative tests *)
  Alcotest.check_raises "seq enum 1" Ok
    (fun () ->
       let _ : Term.term =
         try term_of_string st "seq(i : T => i)" with
         | Squirrelcore.Typing.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );
  Alcotest.check_raises "seq enum 2" Ok
    (fun () ->
       let _ : Term.term =
         try term_of_string st "seq(i : int => i)" with
         | Squirrelcore.Typing.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );
  Alcotest.check_raises "seq enum 3" Ok
    (fun () ->
       let _ : Term.term =
         try term_of_string st "seq(i : message => i)" with
         | Squirrelcore.Typing.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );

    ()

(*------------------------------------------------------------------*)
let cycle_detection () =
  let st = Prover.init () in

  (* positive tests *)
  let _ : Prover.state =
    Prover.exec_all ~test:true st "lemma [any] _ x : x = 1." 
  in

  (* negative tests *)
  Alcotest.check_raises "type inferrence cycle 1" Ok
    (fun () ->
       let _ : Prover.state =
         try Prover.exec_all ~test:true st "lemma [any] _ x : x = (x,1)." with
         | Squirrelcore.Typing.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );

  Alcotest.check_raises "type inferrence cycle 2" Ok
    (fun () ->
       let _ : Prover.state =
         try Prover.exec_all ~test:true st "let rec f n =  (f (n-1), empty)." with
         | Squirrelcore.Typing.Error (_, Failure _) -> raise Ok
       in
       raise Ko
    );

  ()


(*------------------------------------------------------------------*)
let tests = [
  ("generic typing" , `Quick, Util.catch_error generic_typing);
  ("namespaces"     , `Quick, Util.catch_error namespaces);
  ("type arguments" , `Quick, Util.catch_error type_arguments);
  ("game parsing"   , `Quick, Util.catch_error crypto_parsing);
  ("let def"        , `Quick, Util.catch_error let_def);
  ("reify"          , `Quick, Util.catch_error reify);
  ("cycle detection", `Quick, Util.catch_error cycle_detection);
]
