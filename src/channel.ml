include Symbols.Channel

type channel = ns Symbols.t
type t = channel

let declare s = ignore (declare_exact s ())

let dummy = declare_exact "ø" ()

let pp_channel ppf c =
  Fmt.pf ppf "%a" (Utils.kw Fmt.(`None)) (Symbols.to_string c)

let () =
  Checks.add_suite "Channel" [
    "Basic", `Quick,
    Symbols.run_restore @@ fun () ->
      Alcotest.check_raises "fails"
        Symbols.Unbound_identifier (fun () -> ignore (of_string "c")) ;
      Alcotest.check_raises "fails"
        Symbols.Unbound_identifier (fun () -> ignore (of_string "d")) ;
      declare "c" ;
      Alcotest.check_raises "fails"
        Symbols.Unbound_identifier (fun () -> ignore (of_string "d")) ;
      ignore (of_string "c") ;
      Alcotest.check_raises "fails"
        Symbols.Multiple_declarations (fun () -> declare "c") ;
      declare "d" ;
      Alcotest.(check bool) "same channels"
        (of_string "c" = of_string "c")
        true ;
      Alcotest.(check bool) "same channels"
        (of_string "d" = of_string "d")
        true ;
      Alcotest.(check bool)
        "not the same channels"
        (of_string "c" = of_string "d")
        false
  ]
