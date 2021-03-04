include Symbols.Channel

module L = Location

(*------------------------------------------------------------------*)
type channel = ns Symbols.t
type t = channel

let declare table s = fst (declare_exact table s ())

let pp_channel ppf c =
  Fmt.pf ppf "%a" (Utils.kw Fmt.(`None)) (Symbols.to_string c)

let fail : 'a -> unit = function _ -> assert false

(*------------------------------------------------------------------*)
type p_channel = string Location.located
    
(*------------------------------------------------------------------*)
(** {2 Test Suit} *)

let () =
  let mk c = L.mk_loc L._dummy c in      
  let table_c = declare Symbols.builtins_table (mk "c") in  
  let table_cd = declare table_c (mk "d") in

  Checks.add_suite "Channel" [
    "Basic", `Quick,
    fun () ->
      ignore (declare (Symbols.builtins_table) (mk "a"));
      Alcotest.check_raises "fails"
        Symbols.(SymbError (L._dummy,Unbound_identifier "c"))
        (fun () -> 
           ignore (of_lsymb (mk "c") Symbols.builtins_table [@coverage off])) ;
      Alcotest.check_raises "fails"
        Symbols.(SymbError (L._dummy,Unbound_identifier "d"))
        (fun () -> 
           ignore (of_lsymb (mk "d") Symbols.builtins_table [@coverage off])) ;

      Alcotest.check_raises "fails"
        Symbols.(SymbError (L._dummy,Unbound_identifier "d"))
        (fun () -> 
           ignore (of_lsymb (mk "d") table_c [@coverage off])) ;
      ignore (of_lsymb (mk "c") table_c) ;
      Alcotest.check_raises "fails"
        Symbols.(SymbError (L._dummy, Multiple_declarations "c"))
        (fun () -> ignore (declare table_c (mk "c"))) ;

      Alcotest.(check bool) "same channels"
        (of_lsymb (mk "c") table_cd = of_lsymb (mk "c") table_cd)
        true ;
      Alcotest.(check bool) "same channels"
        (of_lsymb (mk "d") table_cd = of_lsymb (mk "d") table_cd)
        true ;
      Alcotest.(check bool)
        "not the same channels"
        (of_lsymb (mk "c") table_cd = of_lsymb (mk "d") table_cd)
        false
  ]
