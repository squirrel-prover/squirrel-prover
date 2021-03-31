module L = Location
type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
let pp_type fmt (l : (Type.esort * int) list) =
  let pp_single fmt (k,i) = match i with
    | 0 -> ()
    | i ->
      assert (i > 0);
      Fmt.pf fmt "%a^%d" Type.pp_e k i
  in
  (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt " →@ ") pp_single) fmt l

let pp_args fmt (l : (string * Type.esort) list) =
  let pp_single fmt (s,k) = Fmt.pf fmt "(%s : %a)" s Type.pp_e k in
  (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt " →@ ") pp_single) fmt l

(*------------------------------------------------------------------*)
type macro_decl = lsymb * (lsymb * Type.esort) list * Type.esort * Theory.term

let pp_macro_decl fmt (s, args, k, t) =
  Fmt.pf fmt "@[<hov 2>term %s : %a → %a =@ %a@]" (L.unloc s)
    pp_args (List.map (fun (x,y) -> (L.unloc x, y)) args)
    Type.pp_e k Theory.pp t

(*------------------------------------------------------------------*)
type abstract_decl = { name          : lsymb;
                       index_arity   : int;
                       message_arity : int; }

let pp_abstract_decl fmt decl =
  Fmt.pf fmt "@[<hov 2>abstract %s : %a → %a@]"
    (L.unloc decl.name)
    pp_type [ (Type.eindex, decl.index_arity);
              (Type.emessage, decl.message_arity) ]
    Type.pp_e Type.emessage

(*------------------------------------------------------------------*)
type goal_decl = { gname   : lsymb option ;
                   gsystem : SystemExpr.p_system_expr ;
                   gform   : Theory.formula ; }

let pp_goal_decl fmt decl =
  let name = match decl.gname with
    | Some s -> L.unloc s
    | None -> "_?" in
  Fmt.pf fmt "@[<hov 2>axiom [%a] %s =@ %a@]"
    SystemExpr.pp_p_system decl.gsystem
    name
    Theory.pp decl.gform

(*------------------------------------------------------------------*)
type system_decl = { sname    : Theory.lsymb option;
                     sprocess : Process.process; }

let pp_system_decl fmt sys =
  let name = match sys.sname with
    | Some s -> L.unloc s
    | None -> "default" in
  Fmt.pf fmt "@[<hov 2>system %s =@ %a@]"
    name
    Process.pp_process sys.sprocess

(*------------------------------------------------------------------*)
type orcl_tag_info = Theory.formula

let pp_orcl_tag_info = Theory.pp

(*------------------------------------------------------------------*)
type declaration_i =
  | Decl_channel of lsymb
  | Decl_process of lsymb * (lsymb * Type.esort) list * Process.process
  | Decl_axiom   of goal_decl
  | Decl_system  of system_decl

  | Decl_hash             of int option * lsymb * orcl_tag_info option
  | Decl_aenc             of lsymb * lsymb * lsymb
  | Decl_senc             of lsymb * lsymb
  | Decl_senc_w_join_hash of lsymb * lsymb * lsymb
  | Decl_sign             of lsymb * lsymb * lsymb * orcl_tag_info option
  | Decl_name             of lsymb * int
  | Decl_state            of macro_decl
  | Decl_abstract         of abstract_decl
  | Decl_macro            of macro_decl

type declaration = declaration_i Location.located

type declarations = declaration list

(*------------------------------------------------------------------*)
let pp_decl fmt decl = match Location.unloc decl with
  | Decl_channel c -> Fmt.pf fmt "channel %s" (L.unloc c)
  | Decl_process (pid, pkind, p) ->
    Fmt.pf fmt "@[<hov 2>process %s %a =@ %a@]"
      (L.unloc pid)
      Process.pp_pkind (List.map (fun (x,y) -> (L.unloc x, y)) pkind)
      Process.pp_process p

  | Decl_axiom decl -> pp_goal_decl fmt decl
  | Decl_system sys -> pp_system_decl fmt sys

  | Decl_hash (i,n,t) ->
    let pp_ar fmt = function
      | None -> ()
      | Some a -> Fmt.pf fmt "%d" a in
    begin
      match t with
      | None ->
        Fmt.pf fmt "@[<hov 2>hash %s %a@]" (L.unloc n) pp_ar i
      | Some t ->
        Fmt.pf fmt "@[<hov 2>hash %s %a with tag@ %a@]"
          (L.unloc n) pp_ar i pp_orcl_tag_info t
    end

  | Decl_aenc (s,d,p) ->
    Fmt.pf fmt "@[<hov 2>aenc %s, %s, %s@]" 
      (L.unloc s) (L.unloc d) (L.unloc p)

  | Decl_senc (s,d) ->
    Fmt.pf fmt "@[<hov 2>senc %s, %s@]" (L.unloc s) (L.unloc d)

  | Decl_senc_w_join_hash (s,d,h) ->
    Fmt.pf fmt "@[<hov 2>senc %s, %s with hash %s@]"
      (L.unloc s) (L.unloc d) (L.unloc h)

  | Decl_sign (s,c,p,t) ->
    begin
      match t with
      | None ->
        Fmt.pf fmt "@[<hov 2>sign %s, %s, %s@]" 
          (L.unloc s) (L.unloc c) (L.unloc p)
      | Some t ->
        Fmt.pf fmt "@[<hov 2>sign %s, %s, %s with tag@ %a@]"
          (L.unloc s) (L.unloc c) (L.unloc p) pp_orcl_tag_info t
    end

  | Decl_name (s,i) ->
    Fmt.pf fmt "@[<hov 2>name %s : %a → %a@]"
      (L.unloc s) pp_type [Type.eindex, i] Type.pp_e Type.emessage
  | Decl_state decl -> pp_macro_decl fmt decl
  (* | Decl_state (s,i,k) ->
    Fmt.pf fmt "@[<hov 2>mutable %s : %a → %a@]"
      s pp_type [Type.eindex, i] Type.pp_e k *)
  | Decl_abstract decl -> pp_abstract_decl fmt decl
  | Decl_macro decl -> pp_macro_decl fmt decl

let pp_decls fmt decls =
  Fmt.pf fmt "@[<v 0>%a@]"
  (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt "@;@") pp_decl) decls
