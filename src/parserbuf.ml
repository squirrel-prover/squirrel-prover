(** Module instantiating parsing from buffers.
 *)

let () = Printexc.record_backtrace true

(** Generic exception for user errors, that should be reported
  * with the given explanation. *)
exception Error of string

(** Given an exception raised during parsing,
  * and a pretty-printer for the location of the error,
  * return [Some pp] where [pp] is a pretty-printer
  * describing the error to the user.
  *
  * For bad, internal errors that should be
  * reported with a backtrace, return [None]. *)
let pp_error pp_loc e = match e with
  | Parser.Error ->
      Some (fun ppf () ->
              Fmt.pf ppf
                "@[Syntax error %a.@]@."
                pp_loc ())
  | Failure s ->
      Some (fun ppf () ->
              Fmt.pf ppf
                "@[Error %a: @,%s.@]@."
                pp_loc ()
                s)
  | Symbols.Unbound_identifier s->
      Some (fun ppf () ->
              Fmt.pf ppf
                "@[Unbound identifier %a : %s.@]@."
                pp_loc ()
                s)
  | Symbols.Multiple_declarations s ->
      Some (fun ppf () ->
              Fmt.pf ppf
                "@[Multiple declarations %a : %s.@]@."
                pp_loc ()
                s)
  | Theory.Conv err ->
      Some (fun ppf () ->
              Fmt.pf ppf
                "@[Error %a: %a.@]@."
                pp_loc ()
                Theory.pp_error err)
  | _ -> None

(** Pretty-printer for parsing locations. *)
let pp_loc filename lexbuf ppf () =
  Fmt.pf ppf
    "in %s @,\
     at line %d char %d @,\
     before %S"
    filename
    lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
    (lexbuf.Lexing.lex_curr_p.Lexing.pos_cnum -
     lexbuf.Lexing.lex_curr_p.Lexing.pos_bol)
    (Lexing.lexeme lexbuf)

let parse_from_buf
      ?(test=false) ?(interactive=false) parse_fun lexbuf filename =
  try parse_fun Lexer.token lexbuf with e ->
    let pp_loc = pp_loc filename lexbuf in
      match pp_error pp_loc e with
        | Some pp_error ->
            if test then raise e else
            if interactive then
              let msg = Fmt.strf "%a" pp_error () in
                raise (Error msg)
            else begin
              Printer.prt `Error "%a" pp_error () ;
              exit 1
            end
        | None ->
            if test || interactive then raise e else begin
              Printer.prt `Error
                "@[Exception %a: @,%s.@]@.@.\
                 %s@."
                pp_loc ()
                (Printexc.to_string e)
                (Printexc.get_backtrace ()) ;
              exit 1
            end

(** Testing *)

let parse_theory_buf ?(test=false) lexbuf filename =
  Process.reset () ;
  parse_from_buf ~test Parser.theory lexbuf filename

let parse_theory_test ?(test=false) filename =
  let lexbuf = Lexing.from_channel (Pervasives.open_in filename) in
  parse_theory_buf ~test lexbuf filename

let parse parser parser_name string =
  let lexbuf = Lexing.from_string string in
  try
    parser Lexer.token lexbuf
  with Parser.Error as e ->
    Format.printf
      "Cannot parse %s before %S at position TODO.@."
      parser_name (Lexing.lexeme lexbuf) ;
    raise e

let parse_process ?(typecheck=false) str =
  let p = parse Parser.top_process "process" str in
    if typecheck then Process.check_proc [] p ;
    p

let parse_formula = parse Parser.top_formula "formula"

let add_suite_restore name suite =
  Checks.add_suite name
    (List.map
       (fun (a,b,c) -> a, b, Symbols.run_restore c)
       suite)

let () =
  let check s =
    Alcotest.(check string) "round-trip" s
      (Format.asprintf "%a" Theory.pp (parse_formula s))
  in
  let eqf s ss =
    let f = parse_formula s in
    let ff = parse_formula ss in
      Alcotest.(check bool) "equal formulas" true
        (f = ff)
  in
  add_suite_restore "Formula parsing" [
    "Boolean constants", `Quick, begin fun () ->
      check "True" ;
      check "False"
    end ;
    "Boolean connectives", `Quick, begin fun () ->
      (* TODO improve without parentheses:
       * the pretty-printer should ideally be aware of precedences
       * between connectives (and quantifiers) and only insert parentheses
       * and boxes when precedences require it  *)
      check "not(True)" ;
      check "(True => False)" ;
      check "(True || False)" ;
      check "((True && True) => False)" ;
    end ;
    "Quantifiers", `Quick, begin fun () ->
      check "forall (x:index), True" ;
      check "forall (x:index), (x = x && x <> x)" ;
      check "exists (x:index), True" ;
      check "exists (x:index,y:message,z:index,t:timestamp), True" ;
      eqf "exists x:index, True" "exists (x:index) True" ;
      check "exists (x,y:index,z:message,\
                     k:index,u,v:timestamp), True" ;
    end
  ]

let () =
  add_suite_restore "Process parsing" [
    "Null", `Quick, begin fun () ->
      ignore (parse_process "null")
    end ;
    "Simple", `Quick, begin fun () ->
      Channel.declare "c" ;
      ignore (parse_process "in(c,x);out(c,x);null") ;
      ignore (parse_process "in(c,x);out(c,x)") ;
      Alcotest.check_raises "fails" Parser.Error
        (fun () -> ignore (parse_process "in(c,x) then null")) ;
      begin match parse_process "(in(c,x);out(c,x) | in(c,x))" with
        | Process.Parallel _ -> ()
        | _ -> assert false
      end ;
      ignore (parse_process
                "if u=true then if True then null else null else null")
    end ;
    "Pairs", `Quick, begin fun () ->
      Channel.declare "c" ;
      ignore (parse_process "in(c,x);out(c,<x,x>)")
    end ;
    "If", `Quick, begin fun () ->
      Channel.declare "c" ;
      Theory.declare_abstract "error" 0 0 ;
      ignore (parse_process "in(c,x); out(c, if x=x then x else error)")
    end ;
    "Try", `Quick, begin fun () ->
      Channel.declare "c" ;
      Theory.declare_state "s" 1 Sorts.emessage ;
      Theory.declare_state "ss" 2 Sorts.emessage ;
      Theory.declare_abstract "error" 0 0 ;
      ignore (parse_process "in(c,x); \
                             try find i such that s(i) = x in \
                               out(c,ss(i,i))
                             else out(c,error)") ;
      ignore (parse_process "in(c,x); \
                             out(c, try find i such that s(i) = x in ss(i,i) \
                                    else error)")
    end
    (* Lost when strongly typing Theory.convert: we do not convert
     * Theory.terms to Term.message, and thus cannot represent constants
     * of type boolean. This should not be too constraining.

    "Facts", `Quick, begin fun () ->
      Theory.declare_abstract "p" [] Sorts.eboolean ;
      Theory.declare_abstract "ok" [] Sorts.emessage ;
      Channel.declare "c" ;
      ignore (parse_process ~typecheck:true
                "if p=true && p()=true then out(c,ok)") ;
      ignore (parse_process ~typecheck:true
                "if p() = p then out(c,ok)")
    end

     *)
  ];;

let () =
  let test = true in
  add_suite_restore "Models" [
    "Null model", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/null.mbc"
    end ;
    "Simple model", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/process.mbc"
    end ;
    "Proc arg", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/process_arg.mbc"
    end ;
    "Proc par", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/process_par.mbc"
    end ;
    "Name declaration", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/name.mbc"
    end ;
    "Pairs", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/pairs.mbc"
    end ;
    "Basic theory", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/theory.mbc"
    end ;
    "Multiple declarations", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Symbols.Multiple_declarations "c")
        (fun () -> parse_theory_test ~test "tests/alcotest/multiple.mbc")
    end ;
    "Action creation", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/actions.mbc" ;
      ignore (Action.find_symbol "IOIO1") ;
      ignore (Action.find_symbol "IOIO2")
      (* TODO test resulting action structure *)
    end ;
    "Let in actions", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/action_let.mbc"
      (* TODO test resulting action structure *)
    end ;
    "New in actions", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/action_name.mbc"
      (* TODO test resulting action structure *)
    end ;
    "Find in actions", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/action_find.mbc"
      (* TODO test resulting action structure *)
    end ;
    "Updates in actions", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/action_set.mbc"
      (* TODO test resulting action structure *)
    end ;
    "LAK model", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/lak.mbc"
    end ;
    "LAK model, again", `Quick, begin fun () ->
      (* We do this again, on purpose, to check that all definitions
       * from the previous run are gone. The macros from Term used
       * to not be re-initialized. *)
      parse_theory_test ~test "tests/alcotest/lak.mbc"
    end ;
    "Local Process", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        Theory.(Conv (Timestamp_unexpected (Var "n")))
        (fun () -> parse_theory_test ~test "tests/alcotest/proc_local.mbc")
    end ;
    "Apply Proc", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
                 Theory.(Conv (Arity_error ("C",1,0)))
      (fun () -> parse_theory_test ~test "tests/alcotest/process_type.mbc")
    end ;
    "Apply Proc", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
                 Theory.(Conv (Undefined "D"))
      (fun () -> parse_theory_test ~test "tests/alcotest/process_nodef.mbc")
    end ;
    "Apply Proc", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Symbols.Multiple_declarations "C")
      (fun () -> parse_theory_test ~test "tests/alcotest/process_mult.mbc")
    end ;
  ];;
