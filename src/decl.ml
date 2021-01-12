let pp_type fmt (l : (Sorts.esort * int) list) =
  let pp_single fmt (k,i) = match i with
    | 0 -> ()
    | i -> 
      assert (i > 0);
      Fmt.pf fmt "%a^%d" Sorts.pp_e k i
  in
  (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt " →@ ") pp_single) fmt l

let pp_args fmt (l : (string * Sorts.esort) list) =
  let pp_single fmt (s,k) = Fmt.pf fmt "(%s : %a)" s Sorts.pp_e k in
  (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt " →@ ") pp_single) fmt l

(*------------------------------------------------------------------*)
type macro_decl = string * (string * Sorts.esort) list * Sorts.esort * Theory.term 

let pp_macro_decl fmt (s, args, k, t) =
  Fmt.pf fmt "@[<hov 2>term %s : %a → %a =@ %a@]" 
    s pp_args args Sorts.pp_e k Theory.pp t

(*------------------------------------------------------------------*)
type abstract_decl = { name          : string;
                       index_arity   : int;
                       message_arity : int; }

let pp_abstract_decl fmt decl =
  Fmt.pf fmt "@[<hov 2>abstract %s : %a → %a@]" 
    decl.name
    pp_type [ (Sorts.eindex, decl.index_arity);
              (Sorts.emessage, decl.message_arity) ]
    Sorts.pp_e Sorts.emessage

(*------------------------------------------------------------------*)
type goal_decl = { gname   : string option ;
                   gsystem : SystemExpr.p_system_expr ;
                   gform   : Theory.formula ; }

let pp_goal_decl fmt decl =
  let name = match decl.gname with
    | Some s -> s
    | None -> "_?" in
  Fmt.pf fmt "@[<hov 2>axiom [%a] %s =@ %a@]"
    SystemExpr.pp_p_system decl.gsystem
    name
    Theory.pp decl.gform

(*------------------------------------------------------------------*)
type system_decl = { sname    : string option;
                     sprocess : Process.process; }

let pp_system_decl fmt sys = 
  let name = match sys.sname with
    | Some s -> s
    | None -> "_?" in
  Fmt.pf fmt "@[<hov 2>system %s =@ %a@]"
    name
    Process.pp_process sys.sprocess

(*------------------------------------------------------------------*)
type orcl_tag_info = Theory.formula

let pp_orcl_tag_info = Theory.pp

(*------------------------------------------------------------------*)
type declaration =
  | Decl_channel of string
  | Decl_process of Process.id * Process.pkind * Process.process
  | Decl_axiom   of goal_decl
  | Decl_system  of system_decl

  | Decl_hash             of int option * string * orcl_tag_info option
  | Decl_aenc             of string * string * string
  | Decl_senc             of string * string                 
  | Decl_senc_w_join_hash of string * string * string
  | Decl_sign             of string * string * string * orcl_tag_info option
  | Decl_name             of string * int 
  | Decl_state            of string * int * Sorts.esort
  | Decl_abstract         of abstract_decl
  | Decl_macro            of macro_decl

type declarations = declaration list

let pp_decl fmt = function
  | Decl_channel c -> Fmt.pf fmt "channel %s" c
  | Decl_process (pid, pkind, p) -> 
    Fmt.pf fmt "@[<hov 2>process %s %a =@ %a@]" 
      pid Process.pp_pkind pkind Process.pp_process p

  | Decl_axiom decl -> pp_goal_decl fmt decl
  | Decl_system sys -> pp_system_decl fmt sys

  | Decl_hash (i,n,t) ->
    let pp_ar fmt = function
      | None -> ()
      | Some a -> Fmt.pf fmt "%d" a in
    begin
      match t with
      | None -> 
        Fmt.pf fmt "@[<hov 2>hash %s %a@]" n pp_ar i
      | Some t -> 
        Fmt.pf fmt "@[<hov 2>hash %s %a with tag@ %a@]" 
          n pp_ar i pp_orcl_tag_info t
    end

  | Decl_aenc (s,d,p) ->
    Fmt.pf fmt "@[<hov 2>aenc %s, %s, %s@]" s d p
  | Decl_senc (s,d) ->
    Fmt.pf fmt "@[<hov 2>senc %s, %s@]" s d 
  | Decl_senc_w_join_hash (s,d,h) ->
    Fmt.pf fmt "@[<hov 2>senc %s, %s with hash %s@]" s d h
  | Decl_sign (s,c,p,t) -> 
    begin
      match t with
      | None -> 
        Fmt.pf fmt "@[<hov 2>sign %s, %s, %s@]" s c p
      | Some t -> 
        Fmt.pf fmt "@[<hov 2>sign %s, %s, %s with tag@ %a@]" 
          s c p pp_orcl_tag_info t
    end

  | Decl_name (s,i) ->
    Fmt.pf fmt "@[<hov 2>name %s : %a → %a@]" 
      s pp_type [Sorts.eindex, i] Sorts.pp_e Sorts.emessage
  | Decl_state (s,i,k) ->
    Fmt.pf fmt "@[<hov 2>mutable %s : %a → %a@]" 
      s pp_type [Sorts.eindex, i] Sorts.pp_e k
  | Decl_abstract decl -> pp_abstract_decl fmt decl
  | Decl_macro decl -> pp_macro_decl fmt decl

let pp_decls fmt decls =
  Fmt.pf fmt "@[<v 0>%a@]"
  (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt "@;@") pp_decl) decls
