type channel = string
type t = channel

let channels : (channel,unit) Hashtbl.t = Hashtbl.create 13

let reset () = Hashtbl.reset channels

let declare s =
  try
    Hashtbl.find channels s ;
    failwith "multiple declarations"
  with Not_found ->
    Hashtbl.add channels s ()

let of_string s = Hashtbl.find channels s ; s

let pp_channel ppf c = Fmt.pf ppf "%a" (Utils.kw Fmt.(`None)) c

let () =
  Checks.add_suite "Channel" [
    "Basic", `Quick,
    fun () ->
      assert (0 = Hashtbl.length channels) ;
      Alcotest.check_raises "fails"
        Not_found (fun () -> ignore (of_string "c")) ;
      Alcotest.check_raises "fails"
        Not_found (fun () -> ignore (of_string "d")) ;
      declare "c" ;
      Alcotest.check_raises "fails"
        Not_found (fun () -> ignore (of_string "d")) ;
      ignore (of_string "c") ;
      Alcotest.check_raises "fails"
        (Failure "multiple declarations") (fun () -> declare "c") ;
      declare "d" ;
      Alcotest.(check string) "same channels"
        (of_string "c") (of_string "c") ;
      Alcotest.(check string) "same channels"
        (of_string "d") (of_string "d") ;
      Alcotest.(check (neg string))
        "not the same channels"
        (of_string "c") (of_string "d") ;
      reset ()
  ]
