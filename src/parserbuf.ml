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
(** Pretty-printer for parsing locations. *)
let pp_error pp_loc pp_pref_loc e = match e with
  | Parser.Error ->
      Some (fun ppf () ->
              Fmt.pf ppf
                "@[%aSyntax error %a.@]@."
                pp_pref_loc ()
                pp_loc ())
  | Failure s ->
      Some (fun ppf () ->
              Fmt.pf ppf
                "@[%aError %a: @,%s.@]@."
                pp_pref_loc ()
                pp_loc ()
                s)
  | Symbols.Unbound_identifier s->
      Some (fun ppf () ->
              Fmt.pf ppf
                "@[%aUnbound identifier %a : %s.@]@."
                pp_pref_loc ()
                pp_loc ()
                s)
  | Theory.Conv err ->
      Some (fun ppf () ->
              Fmt.pf ppf
                "@[%aError %a: %a.@]@."
                pp_pref_loc ()
                pp_loc ()
                Theory.pp_error err)
  | _ -> None

let pp_loc interactive filename lexbuf ppf () =
  if not(interactive) then
    Fmt.pf ppf
      " in %s @,\
       at line %d char %d @,\
       before %S"
      filename
      lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
      (lexbuf.Lexing.lex_curr_p.Lexing.pos_cnum -
       lexbuf.Lexing.lex_curr_p.Lexing.pos_bol)
      (Lexing.lexeme lexbuf)
  else
    Fmt.pf ppf
      "at line %d char %d of this input @,\
       before %S"
      lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
      (lexbuf.Lexing.lex_curr_p.Lexing.pos_cnum -
       lexbuf.Lexing.lex_curr_p.Lexing.pos_bol)
      (Lexing.lexeme lexbuf)

let pp_pref_loc interactive lexbuf ppf () =
  if interactive then
        Fmt.pf ppf
      "[error-%d-%d]"
      (Lexing.lexeme_start_p lexbuf).pos_cnum
      (Lexing.lexeme_end_p lexbuf).pos_cnum


let parse_from_buf
      ?(test=false) ?(interactive=false) parse_fun lexbuf filename =
  try parse_fun Lexer.token lexbuf with e ->
    let pp_loc = pp_loc interactive filename lexbuf in
    let pp_pref_loc = pp_pref_loc interactive lexbuf in
      match pp_error pp_loc pp_pref_loc e with
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
  parse_from_buf ~test Parser.declarations lexbuf filename

let parse_theory_test ?(test=false) filename =
  let lexbuf = Lexing.from_channel (Stdlib.open_in filename) in
  let decls = parse_theory_buf ~test lexbuf filename in
  Prover.declare_list Symbols.builtins_table decls

let parse parser parser_name string =
  let lexbuf = Lexing.from_string string in
  try
    parser Lexer.token lexbuf
  with Parser.Error as e ->
    Format.printf
      "Cannot parse %s before %S at position TODO.@."
      parser_name (Lexing.lexeme lexbuf) ;
    raise e

let parse_process table ?(typecheck=false) str =
  let p = parse Parser.top_process "process" str in
    if typecheck then Process.check_proc table [] p ;
    p

let parse_formula = parse Parser.top_formula "formula"

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
  Checks.add_suite "Formula parsing" [
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
  let table = Channel.declare Symbols.builtins_table "c" in

  Checks.add_suite "Process parsing" [
    "Null", `Quick, begin fun () ->
      ignore (parse_process table "null" : Process.process)
    end ;
    "Simple", `Quick, begin fun () ->
      ignore (parse_process table "in(c,x);out(c,x);null" : Process.process) ;
      ignore (parse_process table "in(c,x);out(c,x)" : Process.process) ;
      Alcotest.check_raises "fails" Parser.Error
        (fun () -> 
           ignore (parse_process table "in(c,x) then null" : Process.process)) ;
      begin match parse_process table "(in(c,x);out(c,x) | in(c,x))" with
        | Process.Parallel _ -> ()
        | _ -> assert false
      end ;
      ignore (parse_process table 
                "if u=true then if True then null else null else null" 
              : Process.process)
    end ;
    "Pairs", `Quick, begin fun () ->
      ignore (parse_process table "in(c,x);out(c,<x,x>)" : Process.process)
    end ;
    "If", `Quick, begin fun () ->
      let table = 
        Prover.declare
          table Decl.(Decl_abstract { name = "error";
                                      index_arity = 0;
                                      message_arity = 0;}) in
      ignore (parse_process table "in(c,x); out(c, if x=x then x else error)" 
              : Process.process)
    end ;
    "Try", `Quick, begin fun () ->
      let table = 
        Prover.declare table Decl.(Decl_state ("s", 1, Sorts.emessage)) in
      let table = 
        Prover.declare table Decl.(Decl_state ("ss", 2, Sorts.emessage)) in
      let table = 
        Prover.declare table Decl.(Decl_abstract { name = "error";
                                                   index_arity = 0;
                                                   message_arity = 0;}) in
      ignore (parse_process table
                "in(c,x); \
                 try find i such that s(i) = x in \
                 out(c,ss(i,i))\
                 else out(c,error)"
              : Process.process) ;
      ignore (parse_process table
                "in(c,x); \
                 out(c, try find i such that s(i) = x in ss(i,i) \
                 else error)"
              : Process.process)
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
  Checks.add_suite "Models" [
    "Null model", `Quick, begin fun () ->
      ignore (parse_theory_test ~test "tests/alcotest/null.sp"
              : Symbols.table )
    end ;
    "Simple model", `Quick, begin fun () ->
      ignore (parse_theory_test ~test "tests/alcotest/process.sp"
              : Symbols.table )
    end ;
    "Proc arg", `Quick, begin fun () ->
      ignore (parse_theory_test ~test "tests/alcotest/process_arg.sp"
              : Symbols.table )
    end ;
    "Proc par", `Quick, begin fun () ->
      ignore (parse_theory_test ~test "tests/alcotest/process_par.sp"
              : Symbols.table )
    end ;
    "Name declaration", `Quick, begin fun () ->
      ignore (parse_theory_test ~test "tests/alcotest/name.sp"
              : Symbols.table )
    end ;
    "Pairs", `Quick, begin fun () ->
      ignore (parse_theory_test ~test "tests/alcotest/pairs.sp"
              : Symbols.table )
    end ;
    "Basic theory", `Quick, begin fun () ->
      ignore (parse_theory_test ~test "tests/alcotest/theory.sp"
              : Symbols.table )
    end ;
    "Multiple declarations", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Prover.Decl_error (Multiple_declarations "c"))
        (fun () -> 
           ignore (parse_theory_test ~test "tests/alcotest/multiple.sp"
                   : Symbols.table ))
    end ;
    "Action creation", `Quick, begin fun () ->
      let table = parse_theory_test ~test "tests/alcotest/actions.sp" in
      ignore (Action.find_symbol "IOIO1" table) ;
      ignore (Action.find_symbol "IOIO2" table)
      (* TODO test resulting action structure *)
    end ;
    "Let in actions", `Quick, begin fun () ->
      ignore (parse_theory_test ~test "tests/alcotest/action_let.sp"
              : Symbols.table )
      (* TODO test resulting action structure *)
    end ;
    "New in actions", `Quick, begin fun () ->
      ignore (parse_theory_test ~test "tests/alcotest/action_name.sp"
              : Symbols.table )
      (* TODO test resulting action structure *)
    end ;
    "Find in actions", `Quick, begin fun () ->
      ignore (parse_theory_test ~test "tests/alcotest/action_find.sp"
              : Symbols.table )
      (* TODO test resulting action structure *)
    end ;
    "Updates in actions", `Quick, begin fun () ->
      ignore (parse_theory_test ~test "tests/alcotest/action_set.sp"
              : Symbols.table )
      (* TODO test resulting action structure *)
    end ;
    "LAK model", `Quick, begin fun () ->
      ignore (parse_theory_test ~test "tests/alcotest/lak.sp"
              : Symbols.table )
    end ;
    "LAK model, again", `Quick, begin fun () ->
      (* We do this again, on purpose, to check that all definitions
       * from the previous run are gone. The macros from Term used
       * to not be re-initialized. *)
      ignore (parse_theory_test ~test "tests/alcotest/lak.sp"
              : Symbols.table )
    end ;
    "Local Process", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Prover.Decl_error
           (Conv_error (Type_error (App ("n",[]),Sorts.etimestamp))))
        (fun () -> 
           ignore (parse_theory_test ~test "tests/alcotest/proc_local.sp"
                   : Symbols.table ))
    end ;
    "Apply Proc", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Prover.Decl_error (Conv_error (Arity_error ("C",1,0))))
        (fun () ->
           ignore (parse_theory_test ~test "tests/alcotest/process_type.sp"
                   : Symbols.table ))
    end ;
    "Apply Proc", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Prover.Decl_error (Conv_error (Undefined "D")))
        (fun () -> 
           ignore (parse_theory_test ~test "tests/alcotest/process_nodef.sp"
                   : Symbols.table ))
    end ;
    "Apply Proc", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Prover.Decl_error (Multiple_declarations "C"))
        (fun () -> 
           ignore (parse_theory_test ~test "tests/alcotest/process_mult.sp"
                   : Symbols.table ))
    end ;
  ];;
