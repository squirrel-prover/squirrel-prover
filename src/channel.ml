include Symbols.Channel

type channel = ns Symbols.t
type t = channel

let declare table s = fst (declare_exact table s ())

let pp_channel ppf c =
  Fmt.pf ppf "%a" (Utils.kw Fmt.(`None)) (Symbols.to_string c)

let fail : 'a -> unit = function _ -> assert false


(*------------------------------------------------------------------*)
let table_c = declare Symbols.builtins_table "c"

let table_cd = declare table_c "d"

let () =
  Checks.add_suite "Channel" [
    "Basic", `Quick,
    fun () ->
      ignore (declare (Symbols.builtins_table) "a");
      Alcotest.check_raises "fails"
        (Symbols.Unbound_identifier "c")
        (fun () -> 
           ignore (of_string "c" Symbols.builtins_table [@coverage off])) ;
      Alcotest.check_raises "fails"
        (Symbols.Unbound_identifier "d")
        (fun () -> 
           ignore (of_string "d" Symbols.builtins_table [@coverage off])) ;

      Alcotest.check_raises "fails"
        (Symbols.Unbound_identifier "d")
        (fun () -> 
           ignore (of_string "d" table_c [@coverage off])) ;
      ignore (of_string "c" table_c) ;
      Alcotest.check_raises "fails"
        (Symbols.Multiple_declarations "c")
        (fun () -> ignore (declare table_c "c")) ;

      Alcotest.(check bool) "same channels"
        (of_string "c" table_cd = of_string "c" table_cd)
        true ;
      Alcotest.(check bool) "same channels"
        (of_string "d" table_cd = of_string "d" table_cd)
        true ;
      Alcotest.(check bool)
        "not the same channels"
        (of_string "c" table_cd = of_string "d" table_cd)
        false
  ]
