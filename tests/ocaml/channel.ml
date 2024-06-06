(** Unit tests for the {!Channel} module. *)

open Squirrelcore
module L = Location
open Channel

let channels =
  let mk c = L.mk_loc L._dummy c in      
  let mk_p c = [], mk c in
  let table_c = declare (Symbols.builtins_table ()) (mk "c") in  
  let table_cd = declare table_c (mk "d") in
  [
    "Basic", `Quick,
    fun () ->
      let exception Ok in
      
      ignore (declare ((Symbols.builtins_table ())) (mk "a"));

      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try ignore(convert (Symbols.builtins_table ()) (mk_p "c")) with
           | Symbols.Error (_, Unbound_identifier (_,"c")) -> raise Ok) ;

      Alcotest.check_raises "fails" Ok
        (fun () -> 
           try ignore (convert (Symbols.builtins_table ()) (mk_p "d")) with
           | Symbols.Error (_,Unbound_identifier (_,"d")) -> raise Ok ) ;

      Alcotest.check_raises "fails" Ok 
        (fun () -> 
           try ignore (convert table_c (mk_p "d")) with 
           | Symbols.Error (_,Unbound_identifier (_,"d")) -> raise Ok) ;
      
      ignore (convert table_c (mk_p "c")) ;

      Alcotest.check_raises "fails" Ok
        (fun () ->
           try ignore (declare table_c (mk "c")) with
           | Symbols.Error (_, Multiple_declarations (_,"c",_,_)) -> raise Ok) ;

      Alcotest.(check' bool) ~msg:"same channels"
        ~actual:(convert table_cd (mk_p "c") = convert table_cd (mk_p "c"))
        ~expected:true ;
      Alcotest.(check' bool) ~msg:"same channels"
        ~actual:(convert table_cd (mk_p "d") = convert table_cd (mk_p "d"))
        ~expected:true ;
      Alcotest.(check' bool)
        ~msg:"not the same channels"
        ~actual:(convert table_cd (mk_p "c") = convert table_cd (mk_p "d"))
        ~expected:false
  ]
