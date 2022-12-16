open  Squirrellib
open  Parserbuf

module L = Location
(** Testing *)

let parse_theory_buf ?(test=false) lexbuf filename =
  parse_from_buf ~test Parser.declarations lexbuf ~filename

let parse_theory_test ?(test=false) filename =
  let lexbuf = Lexing.from_channel (Stdlib.open_in filename) in
  let decls = parse_theory_buf ~test lexbuf filename in
  let table, subgs =
    ProcessDecl.declare_list (TConfig.reset_params
                                Symbols.builtins_table) decls
  in
  assert (subgs = []);
  table

let parse parser parser_name string =
  let lexbuf = Lexing.from_string string in
  try
    parser Lexer.token lexbuf
  with Parser.Error as e ->
    Format.printf
      "Cannot parse %s before %S at position TODO."
      parser_name (Lexing.lexeme lexbuf) ;
    raise e

let parse_process (env : Env.t) ?(typecheck=false) str =
  let p = parse Parser.top_process "process" str in
  let projs = [ Term.left_proj; Term.right_proj; ] in
  if typecheck then Process.check_proc env projs p ;
  p

let process_parsing =
  let table = Channel.declare Symbols.builtins_table (L.mk_loc L._dummy "c") in
  let env = Env.init ~table () in

  (* Checks.add_suite "Process parsing" [ *)
  [
    "Null", `Quick, begin fun () ->
      ignore (parse_process env "null" : Process.process)
    end ;
    "Simple", `Quick, begin fun () ->
      ignore (parse_process env "in(c,x);out(c,x);null" : Process.process) ;
      ignore (parse_process env "in(c,x);out(c,x)" : Process.process) ;
      Alcotest.check_raises "fails" Parser.Error
        (fun () ->
           ignore (parse_process env "in(c,x) then null" : Process.process)) ;
      begin
        match
          Location.unloc (parse_process env "(in(c,x);out(c,x) | in(c,x))")
        with
        | Process.Parallel _ -> ()
        | _ -> assert false
      end ;
      ignore (parse_process env
                "if u=true then if true then null else null else null"
              : Process.process)
    end ;
    "Pairs", `Quick, begin fun () ->
      ignore (parse_process env "in(c,x);out(c,<x,x>)" : Process.process)
    end ;
    "If", `Quick, begin fun () ->
      let table, _ =
        let decl_i =
          Decl.Decl_abstract {
            name = L.mk_loc L._dummy "error";
            symb_type = `Prefix;
            ty_args = [];
            abs_tys = L.mk_loc L._dummy Theory.P_message; }
        in
        let decl = Location.mk_loc Location._dummy decl_i in
        ProcessDecl.declare table decl in
      let env = { env with table } in
      ignore (parse_process env "in(c,x); out(c, if x=x then x else error)"
              : Process.process)
    end ;
    "Try", `Quick, begin fun () ->
      let table, _ =
        let decl_i =
          Decl.Decl_abstract
            { name = L.mk_loc L._dummy "ok";
              symb_type = `Prefix;
              ty_args = [];
              abs_tys = L.mk_loc L._dummy Theory.P_message; }
        in
        let decl = Location.mk_loc Location._dummy decl_i in
        ProcessDecl.declare table decl
      in
      
      let table, _ =
        let decl_i =
          Decl.Decl_abstract
            { name = L.mk_loc L._dummy "error";
              symb_type = `Prefix;
              ty_args = [];
              abs_tys = L.mk_loc L._dummy Theory.P_message; }
        in
        
        let decl = Location.mk_loc Location._dummy decl_i in
        ProcessDecl.declare table decl
      in
      let env = { env with table } in
      ignore (parse_process env
                "in(c,x); \
                 try find i such that x = x in \
                 out(c,ok)\
                 else out(c,error)"
              : Process.process) ;
      ignore (parse_process env
                "in(c,x); \
                 out(c, try find i such that x = x in ok \
                 else error)"
              : Process.process)
    end
  ];;

let models =
  let exception Ok in
  let test = true in
  (* Checks.add_suite "Models" [ *)
  [
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
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try
             ignore (parse_theory_test ~test "tests/alcotest/multiple.sp"
                     : Symbols.table )
           with Symbols.Error (_, Multiple_declarations ("c",_,_)) ->
             raise Ok)
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
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try ignore (parse_theory_test ~test "tests/alcotest/proc_local.sp"
                       : Symbols.table )
           with
             Theory.Conv _ -> raise Ok)
    end ;
    "Apply Proc - 0", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok

        (fun () ->
           try ignore (parse_theory_test ~test "tests/alcotest/process_type.sp"
                       : Symbols.table )
           with
             (Process.Error (_,
                             Arity_error ("C",1,0))) ->
             raise Ok)
    end ;
    "Apply Proc - 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try ignore (parse_theory_test ~test "tests/alcotest/process_nodef.sp"
                       : Symbols.table )
           with Symbols.Error (_, Symbols.Unbound_identifier "D") -> raise Ok)
    end ;
    "Apply Proc - 2", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try ignore (parse_theory_test ~test "tests/alcotest/process_mult.sp"
                       : Symbols.table )
           with Symbols.Error (_,
                                   Symbols.Multiple_declarations ("C",_,_)) ->
             raise Ok)
    end ;
    "Duplicated State Update", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try ignore (parse_theory_test ~test
                        "tests/alcotest/state_duplicated_update.sp"
                       : Symbols.table )
           with Process.Error (_,
                               DuplicatedUpdate "s") -> raise Ok)
    end ;
  ];;

