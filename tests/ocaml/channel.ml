(** Unit tests for the {!Channel} module. *)

open Squirrelcore
module L = Location
open Channel

let channels =
  let mk c = L.mk_loc L._dummy c in      
  let table_c = declare Symbols.builtins_table (mk "c") in  
  let table_cd = declare table_c (mk "d") in
  [
    "Basic", `Quick,
    fun () ->
      let exception Ok in
      
      ignore (declare (Symbols.builtins_table) (mk "a"));
      Alcotest.check_raises "fails"
        Symbols.(Error (L._dummy,Unbound_identifier "c"))
        (fun () -> 
           ignore (of_lsymb (mk "c") Symbols.builtins_table [@coverage off])) ;
      Alcotest.check_raises "fails"
        Symbols.(Error (L._dummy,Unbound_identifier "d"))
        (fun () -> 
           ignore (of_lsymb (mk "d") Symbols.builtins_table [@coverage off])) ;

      Alcotest.check_raises "fails"
        Symbols.(Error (L._dummy,Unbound_identifier "d"))
        (fun () -> 
           ignore (of_lsymb (mk "d") table_c [@coverage off])) ;
      ignore (of_lsymb (mk "c") table_c) ;
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try ignore (declare table_c (mk "c")) with
           | Symbols.Error (_, Multiple_declarations ("c",_,_)) -> raise Ok) ;

      Alcotest.(check' bool) ~msg:"same channels"
        ~actual:(of_lsymb (mk "c") table_cd = of_lsymb (mk "c") table_cd)
        ~expected:true ;
      Alcotest.(check' bool) ~msg:"same channels"
        ~actual:(of_lsymb (mk "d") table_cd = of_lsymb (mk "d") table_cd)
        ~expected:true ;
      Alcotest.(check' bool)
        ~msg:"not the same channels"
        ~actual:(of_lsymb (mk "c") table_cd = of_lsymb (mk "d") table_cd)
        ~expected:false
  ]
