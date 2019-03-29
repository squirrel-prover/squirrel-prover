let suites = ref []
let add_suite name lst = suites := (name,lst) :: !suites
let run () =
  Alcotest.run ~argv:Sys.argv "MetaBC" (List.rev !suites)
