module L = Location

(*------------------------------------------------------------------*)
(** Not type safe, do not export.
    [np] is the namespace path, [s] the symbol name. *)
let get_fsymb (p : Symbols.s_path) : Symbols.fname =
  Symbols.Operator.of_s_path p 

let get_btype (s : Symbols.s_path) : Symbols.btype =
  try Symbols.BType.of_s_path s with
  | Symbols.Error _ -> assert false

let mk_zero  f table         = Term.mk_fun table (f table) []
let mk_one   f table x       = Term.mk_fun table (f table) [x]
let mk_two   f table x y     = Term.mk_fun table (f table) [x;y]
let mk_three f table x y z   = Term.mk_fun table (f table) [x;y;z]
let mk_four  f table x y z t = Term.mk_fun table (f table) [x;y;z;t]
(*------------------------------------------------------------------*)
module Prelude = struct
  let mk_fun table str ~ty_args args =
    let symb = get_fsymb str in
    Term.mk_fun table symb ~ty_args args

  let mk_fun_infer_tyargs table str args =
    let symb = get_fsymb str in
    Term.mk_fun_infer_tyargs table symb args

  (*------------------------------------------------------------------*)
  (*------------------------------------------------------------------*)
  
  let witness_p = ([], "witness" )
  let zeroes_p  = ([], "zeroes"  )
  let eq_p      = ([], "="       )
  let neq_p     = ([], "<>"      )
  let leq_p     = ([], "<="      )
  let lt_p      = ([], "<"      )

  let fs_witness = get_fsymb witness_p  
  let fs_zeroes = Symbols.Operator.of_s_path zeroes_p
  let fs_eq      = get_fsymb eq_p
  let fs_neq     = get_fsymb neq_p 
  let fs_leq = Symbols.Operator.of_s_path leq_p
  let fs_lt = Symbols.Operator.of_s_path lt_p           

  let mk_witness table ~ty_arg = mk_fun table witness_p ~ty_args:[ty_arg] []
  let mk_zeroes  table term    = mk_fun table zeroes_p  ~ty_args:[]       [term]  
  let mk_eq      table t1 t2   = mk_fun_infer_tyargs table eq_p  [t1;t2]
  let mk_neq     table t1 t2   = mk_fun_infer_tyargs table neq_p [t1;t2]
  let mk_leq     table t1 t2   = mk_fun_infer_tyargs table leq_p [t1;t2]

  (*------------------------------------------------------------------*)
  let tstring = Type.base [] (Symbols.to_string (get_btype ([],"string")).s)
end

(*------------------------------------------------------------------*)
module Set = struct

  let namespace = []

  let check_load table =
    if not (Symbols.Import.mem_sp (namespace, "Set") table) then
      Tactics.hard_failure (Failure "theory Set is not loaded")

  let get_fsymb table s =
    check_load table;
    get_fsymb (namespace,s)

  let fs_mem      table = get_fsymb table "mem"
  let fs_add      table = get_fsymb table "add"
  let fs_union    table = get_fsymb table "union"
  let fs_subseteq table = get_fsymb table "subseteq"
  let fs_empty    table = get_fsymb table "empty_set"
end  

(*------------------------------------------------------------------*)
module Int = struct
  (* namespace path *)
  let int_p = ["Int"]

  let is_loaded table =
    Symbols.Import.mem_sp ([], "Int") table

  let check_load table =
    if not (Symbols.Import.mem_sp ([],"Int") table) then
      Tactics.hard_failure (Failure "theory Int is not loaded")

  let get_fsymb table s =
    check_load table;
    get_fsymb (int_p,s)

  let get_btype table s =
    check_load table;
    get_btype  (int_p,s)

  let tint table = Type.base [] (Symbols.to_string (get_btype table "int").s)

  (*------------------------------------------------------------------*)
  let add   table = get_fsymb table "+"
  let minus table = get_fsymb table "-"
  let opp   table = get_fsymb table "opp"

  let mul   table = get_fsymb table "*"

  (*------------------------------------------------------------------*)
  let mk_add   table x y = Term.mk_fun table (add table)   [x;y]
  let mk_minus table x y = Term.mk_fun table (minus table) [x;y]
  let mk_opp   table x   = Term.mk_fun table (opp table)   [x]

  let mk_mul   table x y = Term.mk_fun table (mul table)   [x;y]
end

(*------------------------------------------------------------------*)
module[@warning "-32"] Real = struct

  (* namespace path *)
  let real_p = ["Real"]
 
  let check_load table =
    if not (Symbols.Import.mem_sp ([],"Real") table) then
      Tactics.hard_failure (Failure "theory Real is not loaded")

  let get_fsymb table s =
    check_load table;
    get_fsymb (real_p,s)

  let get_btype table s =
    check_load table;
    get_btype  (real_p,s)

  let treal table = Type.base real_p (Symbols.to_string (get_btype table "real").s)

  (*------------------------------------------------------------------*)
  let fs_add   table = get_fsymb table "+"
  let fs_minus table = get_fsymb table "-"
  let fs_opp   table = get_fsymb table "opp"

  let fs_mul   table = get_fsymb table "*"
  let fs_div   table = get_fsymb table "div"
  let fs_inv   table = get_fsymb table "inv"

  let fs_zero  table = get_fsymb table "z_r"
  let fs_one   table = get_fsymb table "o_r"
  let fs_two   table = get_fsymb table "t_r"

  (*------------------------------------------------------------------*)
  let mk_add   table x y = Term.mk_fun table (fs_add table)   [x;y]
  let mk_minus table x y = Term.mk_fun table (fs_minus table) [x;y]
  let mk_opp   table x   = Term.mk_fun table (fs_opp table)   [x]

  let mk_mul   table x y = Term.mk_fun table (fs_mul table)   [x;y]
  let mk_div   table x y = Term.mk_fun table (fs_div table)   [x;y]
  let mk_inv   table x   = Term.mk_fun table (fs_inv table)   [x]

  let mk_zero  table     = Term.mk_fun table (fs_zero table)  []
  let mk_one   table     = Term.mk_fun table (fs_one  table)  []
  let mk_two   table     = Term.mk_fun table (fs_two  table)  []
end

(*------------------------------------------------------------------*)
module Secrecy = struct

  let is_loaded table =
    Symbols.Import.mem_sp ([], "WeakSecrecy") table
  let check_load table =
    if not (is_loaded table) then
      Tactics.hard_failure (Failure "theory WeakSecrecy is not loaded")
        
  let get_predicate table s =
    check_load table;
    Symbols.Predicate.of_s_path ([],s)
  
  let symb_deduce table = get_predicate table "|>"
  let symb_not_deduce table = get_predicate table "*>"
end

(*------------------------------------------------------------------*)
module Logic = struct

  let is_loaded table =
    Symbols.Import.mem_sp ([], "Logic") table
      
  let check_load table =
    if not (is_loaded table) then
      Tactics.hard_failure (Failure "theory Logic is not loaded")


  let get_fsymb table s =
    check_load table;
    get_fsymb ([],s)
  
  let fs_well_founded table = get_fsymb table "well_founded"
end


(*------------------------------------------------------------------*)
module Deduction = struct
  let name = "DeductionSyntax"

  let check_load_deduction_syntax table =
    if not (Symbols.Import.mem_sp ([], name) table) then
      Tactics.hard_failure (Failure "theory DeductionSyntax is not loaded")
        
  let get_predicate table s =
    check_load_deduction_syntax table;
    Symbols.Predicate.of_s_path ([],s)

  let uniform_deduction table = get_predicate table "|1>"
end  

(*------------------------------------------------------------------*)
module Reify = struct

  let check_load table =
    if not (Symbols.Import.mem_sp ([],"Reify") table) then
      Tactics.hard_failure (Failure "theory Reify is not loaded")

  let get_fsymb table ?path:(x = []) s =
    check_load table;
    get_fsymb (x,s)

  let get_btype table ?path:(x = []) s =
    check_load table;
    get_btype  (x,s)

  module StringList = struct
    let ty table =
      Type.base ["StringList"]
                  (Symbols.to_string
                    (get_btype table ~path:["StringList"] "t").s)
    let fs_empty table = get_fsymb table ~path:["StringList"]  "empty"
    let fs_add   table = get_fsymb table ~path:["StringList"]  "add"
    let mk_empty       = mk_zero fs_empty
    let mk_add         = mk_two  fs_add
  end (*StringList*)

  module Ident = struct
    let ty table =
		  Type.base ["Ident"]
								  (Symbols.to_string
									  (get_btype table ~path:["Ident"] "t").s)
    let fs_ident table = get_fsymb table ~path:["Ident"]  "ident"
    let mk_ident       = mk_two fs_ident
  end (*ident*)

  module Tvar = struct
    let ty table =
		  Type.base ["Tvar"]
								  (Symbols.to_string
									  (get_btype table ~path:["Tvar"] "t").s)
    let fs_tvar table = get_fsymb table ~path:["Tvar"]  "tvar"
    let mk_tvar       = mk_one fs_tvar
  end (*Tvar*)

  module Ty = struct
    let ty table =
		  Type.base ["Type"]
		              (Symbols.to_string
                    (get_btype table ~path:["Type"] "t").s)

    module List = struct
      let ty table =
        Type.base ["Type";"List"]
                    (Symbols.to_string
                      (get_btype table ~path:["Type";"List"] "t").s)
      let fs_empty table = get_fsymb table ~path:["Type";"List"]  "empty"
      let fs_add   table = get_fsymb table ~path:["Type";"List"]  "add"
      let mk_empty       = mk_zero fs_empty
      let mk_add         = mk_two  fs_add
    end (*List*)

    let fs_message   table = get_fsymb table ~path:["Type"]  "Message"
    let fs_boolean   table = get_fsymb table ~path:["Type"]  "Boolean"
    let fs_index     table = get_fsymb table ~path:["Type"]  "Index"
    let fs_timestamp table = get_fsymb table ~path:["Type"]  "Timestamp"
    let fs_tbase     table = get_fsymb table ~path:["Type"]  "Tbase"
    let fs_tvar      table = get_fsymb table ~path:["Type"]  "Tvar"
    let fs_tuple     table = get_fsymb table ~path:["Type"]  "Tuple"
    let fs_func      table = get_fsymb table ~path:["Type"]  "Fun"

    let mk_message         = mk_zero fs_message
    let mk_boolean         = mk_zero fs_boolean
    let mk_index           = mk_zero fs_index
    let mk_timestamp       = mk_zero fs_timestamp
    let mk_tbase           = mk_two  fs_tbase
    let mk_tvar            = mk_one  fs_tvar
    let mk_tuple           = mk_one  fs_tuple
    let mk_func            = mk_two  fs_func
  end (*Type*)

  module Var = struct
    let ty table =
      Type.base ["Var"]
                  (Symbols.to_string
                    (get_btype table ~path:["Var"] "t").s)
    let fs_cons table = get_fsymb table ~path:["Var"]  "cons"
    let mk_cons       = mk_one fs_cons
  end (*Var*)

  module Binder = struct
    let ty table =
      Type.base ["Binder"]
                  (Symbols.to_string
                    (get_btype table ~path:["Binder"] "t").s)
    let fs_cons table = get_fsymb table ~path:["Binder"]  "cons"
    let mk_cons       = mk_two fs_cons

    module List = struct
      let ty table =
        Type.base ["Binder";"List"]
                    (Symbols.to_string
                      (get_btype table ~path:["Binder";"List"] "t").s)
      let fs_empty table = get_fsymb table ~path:["Binder";"List"]  "empty"
      let fs_add   table = get_fsymb table ~path:["Binder";"List"]  "add"
      let mk_empty    = mk_zero fs_empty
      let mk_add      = mk_two  fs_add
    end (*List*)
  end (*Binder*)

  module Quant = struct
    let ty table =
      Type.base ["Quant"]
                  (Symbols.to_string
                    (get_btype table ~path:["Quant"] "t").s)
    let fs_forall      table = get_fsymb table ~path:["Quant"]  "ForAll"
    let fs_exsitential table = get_fsymb table ~path:["Quant"]  "Exsitential"
    let fs_seq         table = get_fsymb table ~path:["Quant"]  "Seq"
    let fs_lambda      table = get_fsymb table ~path:["Quant"]  "Lambda"
    let mk_forall            = mk_zero fs_forall
    let mk_existential       = mk_zero fs_exsitential
    let mk_seq               = mk_zero fs_seq
    let mk_lambda            = mk_zero fs_lambda
  end (*Quant*)

  module Projection = struct
      let ty table =
        Type.base ["Projection"]
                    (Symbols.to_string
                      (get_btype table ~path:["Projection"] "t").s)
      let fs_left  table = get_fsymb table ~path:["Projection"]  "Left"
      let fs_right table = get_fsymb table ~path:["Projection"]  "Right"
      let fs_cons table = get_fsymb table ~path:["Projection"]  "Cons"
      let mk_left        = mk_zero fs_left
      let mk_right       = mk_zero  fs_right
      let mk_cons       = mk_one  fs_right
  end (*Projection*)

  module SysVar = struct
    let ty table =
      Type.base ["SysVar"]
        (Symbols.to_string
           (get_btype table ~path:["SysVar"] "t").s)
    let fs_of_ident table = get_fsymb table ~path:["SysVar"]  "Of_ident"
    let fs_set      table = get_fsymb table ~path:["SysVar"]  "set"
    let fs_pair     table = get_fsymb table ~path:["SysVar"]  "pair"
    let mk_of_ident       = mk_one   fs_of_ident
    let mk_set            = mk_zero  fs_set
    let mk_pair           = mk_zero  fs_pair
  end

  module Single = struct
    let ty table =
      Type.base ["Single"]
        (Symbols.to_string
           (get_btype table ~path:["Single"] "t").s)
    let fs_make table = get_fsymb table ~path:["Single"]  "make"
    let mk_make       = mk_two  fs_make
  end

  module CntList = struct
    let ty table =
      Type.base ["CntList"]
        (Symbols.to_string
           (get_btype table ~path:["CntList"] "t").s)
    let fs_empty table = get_fsymb table ~path:["CntList"]  "empty"
    let fs_add   table = get_fsymb table ~path:["CntList"]  "add"
    let mk_empty       = mk_zero  fs_empty
    let mk_add         = mk_two   fs_add
  end

  module Sys = struct
    let ty table =
      Type.base ["Sys"]
        (Symbols.to_string
           (get_btype table ~path:["Sys"] "t").s)
    let fs_var  table = get_fsymb table ~path:["Sys"]  "Var"
    let fs_any  table = get_fsymb table ~path:["Sys"]  "Any"
    let fs_list table = get_fsymb table ~path:["Sys"]  "List"
    let mk_var        = mk_one  fs_var
    let mk_any        = mk_zero fs_any
    let mk_list       = mk_one  fs_list
  end

  module TyDecl = struct
    let ty table =
      Type.base ["TyDecl"]
        (Symbols.to_string
           (get_btype table ~path:["TyDecl"] "t").s)
    let fs_make table = get_fsymb table ~path:["TyDecl"]  "make"
    let mk_make t x ty = Term.mk_fun t  (fs_make t) ~ty_args:[ty] [x]
  end

  module VarDecl = struct
    let ty table =
      Type.base ["VarDecl"]
        (Symbols.to_string
           (get_btype table ~path:["VarDecl"] "t").s)
    let fs_make table = get_fsymb table ~path:["VarDecl"]  "make"
    let mk_make t qx x ty  = Term.mk_fun t (fs_make t) ~ty_args:[ty] [qx;x]
  end

  module SysDecl = struct
    let ty table =
      Type.base ["SysDecl"]
        (Symbols.to_string
           (get_btype table ~path:["SysDecl"] "t").s)
    let fs_make table = get_fsymb table ~path:["SysDecl"]  "make"
    let mk_make       = mk_one  fs_make
  end

  module EvalEnv = struct
    let ty table =
      Type.base ["EvalEnv"]
        (Symbols.to_string
           (get_btype table ~path:["EvalEnv"] "t").s)

    module TyEnv = struct
      let ty table =
        Type.base ["EvalEnv";"TyEnv"]
                    (Symbols.to_string
                      (get_btype table ~path:["EvalEnv";"TyEnv"] "t").s)
      let fs_empty table = get_fsymb table ~path:["EvalEnv";"TyEnv"]  "empty"
      let fs_add   table = get_fsymb table ~path:["EvalEnv";"TyEnv"]  "add"
      let mk_empty       = mk_zero fs_empty
      let mk_add         = mk_two  fs_add
    end (*TyEnv*)

    module VarEnv = struct
      let ty table =
        Type.base ["EvalEnv";"VarEnv"]
                    (Symbols.to_string
                      (get_btype table ~path:["EvalEnv";"VarEnv"] "t").s)
      let fs_empty table = get_fsymb table ~path:["EvalEnv";"VarEnv"]  "empty"
      let fs_add   table = get_fsymb table ~path:["EvalEnv";"VarEnv"]  "add"
      let mk_empty       = mk_zero fs_empty
      let mk_add         = mk_two  fs_add
    end (*VarEnv*)

    module SysEnv = struct
      let ty table =
        Type.base ["EvalEnv";"SysEnv"]
                    (Symbols.to_string
                      (get_btype table ~path:["EvalEnv";"SysEnv"] "t").s)
      let fs_empty table = get_fsymb table ~path:["EvalEnv";"SysEnv"]  "empty"
      let fs_add   table = get_fsymb table ~path:["EvalEnv";"SysEnv"]  "add"
      let mk_empty       = mk_zero fs_empty
      let mk_add         = mk_two  fs_add
    end (*SysEnv*)

    let fs_make table = get_fsymb table ~path:["EvalEnv"]  "make"
    let mk_make       = mk_four  fs_make
  end

  module Term = struct
    let ty table =
      Type.base ["Term"]
                  (Symbols.to_string
                    (get_btype table ~path:["Term"] "t").s)

    let () = Term.set_reify_type ty

    module List = struct
      let ty table =
        Type.base ["Term";"List"]
                    (Symbols.to_string
                      (get_btype table ~path:["Term";"List"] "t").s)
      let fs_empty table = get_fsymb table ~path:["Term";"List"]  "empty"
      let fs_add   table = get_fsymb table ~path:["Term";"List"]  "add"
      let mk_empty       = mk_zero fs_empty
      let mk_add         = mk_two  fs_add
    end (*List*)

    module Diff = struct
      let ty table =
        Type.base ["Term";"Diff"]
                    (Symbols.to_string
                      (get_btype table ~path:["Term";"Diff"] "t").s)
      let fs_empty table = get_fsymb table ~path:["Term";"Diff"]  "empty"
      let fs_add   table = get_fsymb table ~path:["Term";"Diff"]  "add"
      let mk_empty       = mk_zero   fs_empty
      let mk_add         = mk_two  fs_add
    end (*Diff*)

    let fs_int    table = get_fsymb table ~path:["Term"]  "Int"
    let fs_string table = get_fsymb table ~path:["Term"]  "String"
    let fs_app    table = get_fsymb table ~path:["Term"]  "App"
    let fs_func   table = get_fsymb table ~path:["Term"]  "Fun"
    let fs_name   table = get_fsymb table ~path:["Term"]  "Name"
    let fs_macro  table = get_fsymb table ~path:["Term"]  "Macro"
    let fs_action table = get_fsymb table ~path:["Term"]  "Action"
    let fs_var    table = get_fsymb table ~path:["Term"]  "Var"
    let fs_letc   table = get_fsymb table ~path:["Term"]  "Letc"
    let fs_tuple  table = get_fsymb table ~path:["Term"]  "Tuple"
    let fs_proj   table = get_fsymb table ~path:["Term"]  "Proj"
    let fs_diff   table = get_fsymb table ~path:["Term"]  "Diff"
    let fs_find   table = get_fsymb table ~path:["Term"]  "Find"
    let fs_quant  table = get_fsymb table ~path:["Term"]  "Quant"

    let mk_int          = mk_one   fs_int
    let mk_string       = mk_one   fs_string
    let mk_app          = mk_two   fs_app
    let mk_fun          = mk_two   fs_func
    let mk_name         = mk_two   fs_name
    let mk_macro        = mk_three fs_macro
    let mk_action       = mk_two   fs_action
    let mk_var          = mk_one   fs_var
    let mk_let          = mk_three fs_letc
    let mk_tuple        = mk_one   fs_tuple
    let mk_proj         = mk_two   fs_proj
    let mk_diff         = mk_one   fs_diff
    let mk_find         = mk_four  fs_find
    let mk_quant        = mk_three fs_quant
  end

end
