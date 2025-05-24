open Utils
open Ppenv

module L  = Location
module Sv = Vars.Sv
module Mv = Vars.Mv
module SE = SystemExpr

type lsymb = Symbols.lsymb

module Cell = struct
  type t = Symbols.macro * Term.term list
  let pp fmt (m,indices) =
    if indices = [] then Symbols.pp_path fmt m else
      Format.fprintf fmt "%a %a"
        Symbols.pp_path m
        (Fmt.list ~sep:Fmt.sp Term.pp) indices
  let map f (m,l) =
    m, List.map f l
  let fold f x (_,l) =
    List.fold_left f x l
end

module Multicell = struct
  (** One cell per projection, implicitly in the ambient order. *)
  type t = Cell.t list
  let pp fmt = function
    | cell::tl when List.for_all ((=) cell) tl ->
        Cell.pp fmt cell
    | multicell ->
        Format.fprintf fmt "diff%a"
          (Utils.pp_list Cell.pp) multicell
  let map f mc = List.map (Cell.map f) mc
  let fold f x mc =
    List.fold_left
      (fun x c -> Cell.fold f x c)
      x
      mc
end

(*------------------------------------------------------------------*)
(** {2 Process type and operations}*)

(** A typed process *)
type proc =
  | Null
  | New      of Vars.var * Type.ty * proc
  | In       of Symbols.channel * Vars.var * proc
  | Out      of Symbols.channel * Term.term * proc
  | Parallel of proc * proc
  | Set      of Multicell.t * Term.term * proc
  | Let      of Vars.var * Term.term * Type.ty * proc
  | Repl     of Vars.var * proc
  | Exists   of Vars.vars * Term.term * proc * proc
  | Apply    of Symbols.process * Term.term list
  | Lock     of Mutex.Multi.t * proc
  | Unlock   of Mutex.Multi.t * proc
  | Alias    of proc * string

(*------------------------------------------------------------------*)
(* does not recurse *)
let tfold (f : 'a -> proc -> 'a) (a : 'a) (proc : proc) : 'a =
  match proc with
  | Apply _ 
  | Null    -> a

  | New    (_,_,p  ) 
  | Out    (_,_,p  ) 
  | In     (_,_,p  )
  | Set    (_,_,p)
  | Let    (_,_,_,p)
  | Repl   (_,p    )
  | Lock   (_,p    )
  | Unlock (_,p    ) 
  | Alias  (p,_    ) -> f a p

  | Parallel (p1,p2    ) 
  | Exists   (_,_,p1,p2) -> f (f a p1) p2

(* does not recurse *)
let tmap f proc =
  match proc with
  | Null                  -> Null
  | New      (v,ty,p    ) -> New      (v,ty,f p     )
  | In       (c,v,p     ) -> In       (c,v,f p      )
  | Out      (c,t,p     ) -> Out      (c,t,f p      )
  | Parallel (p1,p2     ) -> Parallel (f p1,f p2    )
  | Set      (l,t,p     ) -> Set      (l,t,f p      )
  | Let      (v,t,ty,p  ) -> Let      (v,t,ty,f p   )
  | Repl     (v,p       ) -> Repl     (v,f p        )
  | Exists   (v,t,p1,p2 ) -> Exists   (v,t,f p1,f p2)
  | Apply    (id,args   ) -> Apply    (id, args     )
  | Lock     (m,p       ) -> Lock     (m, f p       )
  | Unlock   (m,p       ) -> Unlock   (m, f p       )
  | Alias    (p,a       ) -> Alias    (f p,a        )

(*------------------------------------------------------------------*)
(** Free term variable *)
let fv (proc : proc) : Sv.t =
  let rec doit (fv : Sv.t) (proc : proc) =
    match proc with
    | New  (v,_,p)
    | In   (_,v,p)
    | Repl (v,p  ) -> Sv.remove v (doit fv p) 

    | Out (_,t,p) -> doit (Sv.union fv (Term.fv t)) p

    | Parallel (p1,p2) -> doit (doit fv p1) p2

    | Set (l,t,p) ->
      let fv = Multicell.fold (fun fv i -> Sv.union fv (Term.fv i)) fv l in
      doit (Sv.union fv (Term.fv t)) p

    | Let (v,t,_,p) ->
      doit (Sv.union fv (Term.fv t)) p |>
      Sv.remove v

    | Exists (vs,t,p1,p2) ->
      let fv = doit (doit fv p1) p2 in
      let fv = Sv.union fv (Term.fv t) in
      List.fold_left ((^~) Sv.remove) fv vs

    | Apply (_,args) -> Sv.union fv (Term.fvs args)

    | Lock (m,p) | Unlock (m,p) -> doit (Sv.union fv (Mutex.Multi.fv m)) p

    | Null | Alias _ -> tfold doit fv proc
  in
  doit Sv.empty proc

(*------------------------------------------------------------------*)
(** Term variable substitution *)
let subst (ts : Term.subst) proc =
  let rec doit ts p =
    match p with
    | New (v, ty, p) -> New (Term.subst_var ts v, ty, doit ts p)

    | In  (c, v , p) ->
      let v, ts = Term.subst_binding v ts in
      In  (c, v, doit ts p)

    | Out (c, t , p) -> Out (c, Term.subst ts t, doit ts p)

    | Set (s, t, p) ->
      Set (Multicell.map (Term.subst ts) s, Term.subst ts t, doit ts p)

    | Let (v, t, ty, p) ->
      let v, ts = Term.subst_binding v ts in
      Let (Term.subst_var ts v, Term.subst ts t, ty, doit ts p)

    | Repl (v, p) ->
      let v, ts = Term.subst_binding v ts in
      Repl (v, doit ts p)

    | Exists (vs, t, p1, p2) ->
      let ts1, vs =
        List.map_fold (fun ts v ->
            let v, ts = Term.subst_binding v ts in
            ts, v
          ) ts vs
      in
      Exists (vs, Term.subst ts1 t, doit ts1 p1, doit ts p2)

    | Apply (id,args) -> Apply (id, List.map (Term.subst ts) args) 

    | Lock (m,p) -> Lock (Mutex.Multi.map (Term.subst_var ts) m, doit ts p)
    
    | Unlock (m,p) -> Unlock (Mutex.Multi.map (Term.subst_var ts) m, doit ts p)

    | Alias _ | Null | Parallel _ -> tmap (doit ts) p
  in
  doit ts proc

(*------------------------------------------------------------------*)
(** Type variable substitution *)
let gsubst (ts : Subst.t) proc =
  let rec doit p =
    match p with
    | New (v, ty, p) -> New (Subst.subst_var ts v, Subst.subst_ty ts ty, doit p)
    | In  (c, v , p) -> In  (c, Subst.subst_var ts v, doit p)
    | Out (c, t , p) -> Out (c, Term.gsubst ts t, doit p)

    | Set (s, t, p) ->
      Set (Multicell.map (Term.gsubst ts) s, Term.gsubst ts t, doit p)

    | Let (v, t, ty, p) ->
      Let (Subst.subst_var ts v, Term.gsubst ts t,Subst.subst_ty ts ty, doit p)

    | Repl (vs, p) -> Repl (Subst.subst_var ts vs, doit p)

    | Exists (vs, t, p1, p2) ->
      Exists (List.map (Subst.subst_var ts) vs,
              Term.gsubst ts t,
              doit p1,
              doit p2)

    | Apply (id,args) -> Apply (id, List.map (Term.gsubst ts) args) 

    | Lock (m,p) -> Lock (Mutex.Multi.map (Subst.subst_var ts) m, doit p)
    
    | Unlock (m,p) -> Unlock (Mutex.Multi.map (Subst.subst_var ts) m, doit p)

    | Alias _ | Null | Parallel _ -> tmap doit p
  in
  doit proc

(*------------------------------------------------------------------*)
(** Pretty-printer *)
let _pp ppe ppf (process : proc) = 
  let rec doit ppf (process : proc) = 
    let open Fmt in
    match process with
    | Null -> Printer.kws `ProcessName ppf "null"

    | Apply (s,l) ->
      pf ppf "@[<hov>%a@ %a@]"
        (Printer.kws `ProcessName) (Symbols.path_to_string s)
        (Fmt.list ~sep:(fun ppf () -> pf ppf "@ ") (Term._pp ppe)) l

    | Alias (p,a) ->
      pf ppf "%s: %a" a doit p

    | Repl (v, p) ->
      let _, v, s = (* rename quantified var. to avoid name clashes *)
        let fv = Sv.remove v (fv p) in
        Term.add_vars_simpl_env (Vars.of_set fv) [v]
      in
      let v = as_seq1 v in
      let p = subst s p in

      pf ppf "@[<hv 2>!_%a(@ @[<hv>%a@])@]"
        (Vars._pp ppe) v doit p

    | Set (multicell, t, p) ->
      pf ppf "@[<hov 2>%a %a@ %a;@]@ %a"
        Multicell.pp multicell
        (Printer.kws `ProcessKeyword) ":="
        (Term._pp ppe) t
        doit p

    | New (v, ty, p) ->
      let _, v, s = (* rename quantified var. to avoid name clashes *)
        let fv = Sv.remove v (fv p) in
        Term.add_vars_simpl_env (Vars.of_set fv) [v]
      in
      let v = as_seq1 v in
      let p = subst s p in

      pf ppf "@[<hov>%a %a : %a;@]@ %a"
        (Printer.kws `ProcessKeyword) "new"
        (Printer.kws `ProcessVariable) (Fmt.str "%a" (Vars._pp ppe) v)
        Type.pp ty
        doit p

    | In (c, v, p) ->
      let _, v, s = (* rename quantified var. to avoid name clashes *)
        let fv = Sv.remove v (fv p) in
        Term.add_vars_simpl_env (Vars.of_set fv) [v]
      in
      let v = as_seq1 v in
      let p = subst s p in

      pf ppf "@[<hov>%a(%a,@,%a);@]@ %a"
        (Printer.kws `ProcessInOut) "in"
        (Printer.kws `ProcessChannel) (Symbols.path_to_string c)
        (Printer.kws `ProcessVariable) (Fmt.str "%a" (Vars._pp ppe) v)
        doit p

    | Out (c, t, p) ->
      pf ppf "@[<hov 2>%a(%a,@,@[%a@]);@]@ %a"
        (Printer.kws `ProcessInOut) "out"
        (Printer.kws `ProcessChannel) (Symbols.path_to_string c)
        (Term._pp ppe) t
        doit p

    | Parallel _ ->
      pf ppf "@[<hv 0>%a@]" doit_chained_parallel process     
      (* pf ppf "@[<hv>@[<hv 2>( %a )@] |@ @[<hv 2>( %a )@]@]" *)
      (*   doit p1 *)
      (*   doit p2 *)

    | Let (v, t, ty, p) ->
      let _, v, s = (* rename quantified var. to avoid name clashes *)
        let fv = Sv.remove v (Sv.union (Term.fv t) (fv p)) in
        Term.add_vars_simpl_env (Vars.of_set fv) [v]
      in
      let v = as_seq1 v in
      let p, t = subst s p, Term.subst s t in

      pf ppf "@[<hov 2>%a %a : %a =@ @[%a@] %a@]@ %a"
        (Printer.kws `ProcessKeyword) "let"
        (Printer.kws `ProcessVariable) (Fmt.str "%a" (Vars._pp ppe) v)
        Type.pp ty
        (Term._pp ppe) t
        (Printer.kws `ProcessKeyword) "in"
        doit p

    | Exists (vs, f, p1, p2) ->
      let _, vs, s = (* rename quantified var. to avoid name clashes *)
        let fv =
          List.fold_left ((^~) Sv.remove) (Sv.union (fv p1) (Term.fv f)) vs
        in
        Term.add_vars_simpl_env (Vars.of_set fv) vs
      in
      let p1, f = subst s p1, Term.subst s f in

      if vs = [] then
        pf ppf "@[<hv>%a %a %a@;<1 2>@[<hv>%a@]"
          (Printer.kws `ProcessCondition) "if"
          (Term._pp ppe) f
          (Printer.kws `ProcessCondition) "then"
          doit p1
      else
        pf ppf "@[<hv>%a %a %a %a %a@;<1 2>@[<hv>%a@]"
          (Printer.kws `ProcessCondition) "find"
          (Utils.pp_list (Vars._pp ppe)) vs
          (Printer.kws `ProcessCondition) "such that"
          (Term._pp ppe) f
          (Printer.kws `ProcessCondition) "in"
          doit p1 ;
      if p2 <> Null then
        pf ppf "@ %a@;<1 2>@[<hv>%a@]@]"
          (Printer.kws `ProcessCondition) "else"
          doit p2
      else
        pf ppf "@]"

    | Lock (m, p) -> 
      pf ppf "@[<hov 2>%a(%a);@]@ %a"
        (Printer.kws `ProcessKeyword) "lock"
        Mutex.Multi.pp m
        doit p

    | Unlock (m, p) -> 
      pf ppf "@[<hov 2>%a(%a);@]@ %a"
        (Printer.kws `ProcessKeyword) "unlock"
        Mutex.Multi.pp m
        doit p

  (* Printing in a [hv 0] box. *)
  and doit_chained_parallel ppf (process : proc) =
    match process with
    | Parallel (p1,p2) ->
      Fmt.pf ppf "@[<hov 2>( %a )@] |@ %a"
        doit                  p1
        doit_chained_parallel p2
      
    | _ -> Fmt.pf ppf "@[<hov 2>%a@]" doit process
    
  in  
  Fmt.pf ppf "@[<hv>%a@]" doit process

(* box [_pp]'s output *)
let _pp ppe fmt p = Fmt.pf fmt "@[<hov> %a@]" (_pp ppe) p
    
let pp_dbg = _pp (default_ppe ~dbg:true  ())
let pp     = _pp (default_ppe ~dbg:false ())

(*------------------------------------------------------------------*)
(** {2 Error handling}*)

type error_i =
  | ArityError          of string * int * int
  | CurrifiedArityError of string * int * int                   
  | StrictAliasError    of string
  | DuplicatedUpdate    of string
  | SyntaxError         of string      
  | ProjsMismatch       of Projection.t list * Projection.t list
  | ActionUndef         of Symbols.action
  | Failure             of string

type error = L.t * error_i

let pp_error_i fmt = function
  | StrictAliasError s -> Fmt.pf fmt "strict alias error: %s" s

  | SyntaxError s -> Fmt.pf fmt "syntax error: %s" s

  | ArityError (s,i,j) -> 
    Fmt.pf fmt "process %s used with arity %i, but \
                defined with arity %i" s i j

  | CurrifiedArityError (s,i,j) -> 
    Fmt.pf fmt "identifier %s used with arity %i, but \
                expected a sequence of arguments (currified) of length %i" s i j


  | DuplicatedUpdate s -> 
    Fmt.pf fmt "state %s can only be updated once in an action" s

  | ProjsMismatch (ps1, ps2) ->
    Fmt.pf fmt "projections mismatch: @[%a@] ≠ @[%a@]"
      Projection.pp_list ps1
      Projection.pp_list ps2

  | ActionUndef a ->
    Fmt.pf fmt "action %a used in the system but not defined"
      Symbols.pp_path a

  | Failure s -> Fmt.pf fmt "%s" s

let pp_error pp_loc_err fmt (loc,e) =
  Fmt.pf fmt "%aProcess error: @[%a@]."
    pp_loc_err loc
    pp_error_i e

exception Error of error

let error ?loc e = raise (Error (odflt L._dummy loc,e))

let () =
  Errors.register (function
    | Error e ->
        Some { printer =
          fun pp_loc_error fmt -> pp_error pp_loc_error fmt e }
    | _ -> None)

(*------------------------------------------------------------------*)
(** {2 Process declaration type}*)

type proc_decl = {
  args  : Vars.vars;
  projs : Projection.t list;
  time  : Vars.var;             (* type timestamp *)
  proc  : proc;
}

(** We extend the symbols data with (bi)-processus descriptions and
    their types. *)
type Symbols.data += Process_data of proc_decl

(*------------------------------------------------------------------*)
let declare_typed table (name : Symbols.lsymb) (pdecl : proc_decl) =
  let data = Process_data pdecl in
  let table, _ = Symbols.Process.declare ~approx:false table name ~data in
  table

(*------------------------------------------------------------------*)
let get_process_data table (p : Symbols.process) =
  match Symbols.Process.get_data p table with
  | Process_data data -> data
  | _ -> assert false
(* The data associated to a process must be a [Process_data _]. *)

(*------------------------------------------------------------------*)
let pp_process_declaration table ~(id : lsymb) (pdecl : proc_decl) : unit =
  let ppe = default_ppe ~table () in
  let pp_args fmt =
    if pdecl.args = [] then () else
      Fmt.pf fmt "(%a) " (Vars._pp_typed_list ppe) pdecl.args
  in
  let pp_projs fmt =
    if pdecl.projs = [] ||
       pdecl.projs = [Projection.left; Projection.right] then ()
    else
      Fmt.pf fmt "@[<:%a>@]@ " Projection.pp_list pdecl.projs
  in
  Printer.pr "@[<v 2>@[%a%t %s %t@]=@ @[%a@]@]@." 
    (Printer.kws `ProcessName) "process"
    pp_projs (L.unloc id) pp_args 
    (_pp ppe) pdecl.proc

(*------------------------------------------------------------------*)
(** {2 Process parsing} *)

module Parse = struct
  (** A parsed process *)
  type cnt =
    | Null
    | New      of lsymb * Typing.ty * t
    | In       of Symbols.p_path * lsymb * t
    | Out      of Symbols.p_path * Typing.term * t
    | Parallel of t * t
    | Set      of (Symbols.p_path * Typing.term list) list * Typing.term * t
    | Let      of lsymb * Typing.term * Typing.ty option * t
    | Repl     of lsymb * t
    | Exists   of lsymb list * Typing.term * t * t
    | Apply    of Symbols.p_path * Typing.term list
    | Lock     of (Symbols.p_path * lsymb list) list * t
    | Unlock   of (Symbols.p_path * lsymb list) list * t
    | Alias    of t * lsymb

  and t = cnt L.located
end

(*------------------------------------------------------------------*)
let convert_process_path table (p : Symbols.p_path) =
  match Symbols.Process.convert1 p table with
  | name, Process_data data -> name, data
  | _ -> assert false
  (* The data associated to a process must be a [Process_data _]. *)

(*------------------------------------------------------------------*)
let is_out_i = function Parse.Out _ -> true | _ -> false
let is_out p = is_out_i (L.unloc p)

(*------------------------------------------------------------------*)

(** Type checking for processes *)
let parse
    table ~(args : Typing.bnds) (projs : Projection.t list) (process : Parse.t)
  : proc_decl
  =

  (* open a typing environment *)
  let ienv = Infer.mk_env () in

  let env = Env.init ~table () in
  let env, args = Typing.convert_bnds ~ienv ~mode:NoTags env args in

  (* create a variable holding the current time-point *)
  let env, time =
    let vars, time =
      Vars.make `Approx env.vars Type.ttimestamp "τ" Vars.Tag.ltag
    in
    { env with vars; }, time
  in
  let cntxt = Typing.InProc (projs, Term.mk_var time) in
  let mk_cenv env = Typing.{ env; cntxt; } in

  let rec doit (ienv : Infer.env) (env : Env.t) (proc : Parse.t) : proc =
    let loc = L.loc proc in
    match L.unloc proc with
    | Parse.Null -> Null

    | Parse.New (x, ty, p) -> 
      let ty = Typing.convert_ty ~ienv env ty in 
      let vars, x = Vars.make_local `Shadow env.vars ty (L.unloc x) in
      New (x, ty, doit ienv { env with vars } p)

    | Parse.In (c,x,p) -> 
      let c = Channel.convert env.table c in
      let vars, x = Vars.make_local `Shadow env.vars (Type.tmessage) (L.unloc x) in
      In (c, x, doit ienv { env with vars } p)

    | Parse.Out (c,m,p)
    | Parse.Alias (L.{ pl_desc = Out (c,m,p) },_) ->
      let c = Channel.convert env.table c in 

      (* raise an error if we are in strict alias mode *)
      if is_out proc && (TConfig.strict_alias_mode env.table) then
        error ~loc (StrictAliasError "missing alias");

      let m, _ =
        Typing.convert ~ienv ~ty:Type.tmessage (mk_cenv env) m 
      in

      let p = doit ienv env p in
      begin
        match L.unloc proc with
        | Alias (_, a) -> Alias (Out (c, m, p), L.unloc a)
        | Out _        -> Out (c, m, p)
        | _ -> assert false
      end

    | Parse.Alias (p,a) -> Alias (doit ienv env p, L.unloc a)

    | Parse.Set (cells, t, p) ->
      let target_ty = ref None in
      let convert_cell (s_p,l) =
        let s = Symbols.Macro.convert_path s_p env.table in
        let nb_args = List.length l in
        begin
          match Symbols.get_macro_data s table with
          | Symbols.State (arity,ty',_) ->
            begin match !target_ty with
            | None -> target_ty := Some ty'
            | Some ty ->
                if ty <> ty' then
                  let msg = "multicells must all have the same type" in
                  Typing.(error loc (Failure msg))
            end;
            (* updating a macro requires to use it in eta-long form *)
            if arity <> nb_args then
              error ~loc:(Symbols.p_path_loc s_p)
                (CurrifiedArityError
                   (Symbols.p_path_to_string s_p,nb_args,arity))
          | _ ->
            Typing.error (Symbols.p_path_loc s_p)
              (Assign_no_state (Symbols.p_path_to_string s_p))
        end;
        s,
        List.map
          (fun x ->
             fst @@ Typing.convert ~ienv ~ty:Type.tindex (mk_cenv env) x)
          l
      in
      let cells = match cells with
        | [] -> assert false
        | [c] -> List.map (fun _proj -> c) projs
        | l -> assert (List.length cells = List.length projs) ; l
      in
      let cells = List.map convert_cell cells in
      let ty = Utils.oget !target_ty in
      let t, _ = Typing.convert ~ienv ~ty (mk_cenv env) t in
      Set (cells, t, doit ienv env p)

    | Parse.Parallel (p, q) ->
      Parallel (doit ienv env p, doit ienv env q)

    | Parse.Let (x, t, ptyo, p) ->
      let ty : Type.ty = match ptyo with
        | None -> Type.univar (Infer.mk_ty_univar ienv)
        | Some pty -> Typing.convert_ty ~ienv env pty 
      in

      let t, _ = Typing.convert ~ienv ~ty (mk_cenv env) t in
      let vars, x = Vars.make_local `Shadow env.vars ty (L.unloc x) in
      Let (x, t, ty, doit ienv { env with vars } p)

    | Parse.Repl (x, p) -> 
      let vars, x = Vars.make_local `Shadow env.vars Type.tindex (L.unloc x) in
      Repl (x, doit ienv { env with vars } p)

    | Parse.Exists (vs, test, p, q) ->
      let q = doit ienv env q in
      let vars, vs =
        List.fold_left_map (fun vars x ->
            let vars, x =
              Vars.make_local `Shadow vars Type.tindex (L.unloc x) in
            vars, x
          ) env.vars vs 
      in
      let env = { env with vars } in
      let test, _ =
        Typing.convert ~ienv ~ty:Type.tboolean (mk_cenv env) test
      in
      let p = doit ienv env p in
      Exists (vs, test, p, q)

    | Parse.Apply (p_id, args') ->
      let args =
        match args' with
          [] -> []
        | [p] -> (match L.unloc p with
            | Typing.Tuple tl -> tl     (* Here, we parsed (x1,...,xn) *)
            | _ -> [p]                  (* Here, we parsed (x) or x *)
          )
        | _ ->
            let msg = "a process identifier must take a tuple as input " in
            error ~loc (SyntaxError msg)
      in      
      let id, p = convert_process_path env.table p_id in

      if projs <> p.projs then
        error ~loc:(L.loc proc) (ProjsMismatch (projs, p.projs));

      let l1, l2 = List.length args, List.length p.args in
      if l1 <> l2 then
        error ~loc:(Symbols.p_path_loc p_id)
          (ArityError (L.unloc @@ snd p_id, l1 , l2));

      let args = 
        List.map2 (fun v t ->
            fst @@ Typing.convert ~ienv ~ty:(Vars.ty v) (mk_cenv env) t
          )
          p.args args
      in

      Apply (id, args)

    | Parse.Lock (mutexes, p)
    | Parse.Unlock (mutexes, p) as cur_p ->
      let mutexes = match mutexes with
        | [] -> assert false
        | [m] -> List.map (fun _proj -> m) projs
        | l -> assert (List.length l = List.length projs) ; l
      in
      let convert_mutex (m,args) proj =
        let s = Symbols.Mutex.convert_path m env.table in
        let l =
          try
            List.map
              (fun symb -> fst @@ as_seq1 (Vars.find env.vars (L.unloc symb)))
              args
          with Not_found -> failwith "illegal mutex index"
        in
        proj, Mutex.make s l env.table
      in
      (* TODO make errors user-friendly: failwith above and Incorrect_arity
         from convert_mutex *)
      begin match cur_p with
        | Parse.Lock _ ->
          Lock (List.map2 convert_mutex mutexes projs, doit ienv env p)
        | _ ->
          Unlock (List.map2 convert_mutex mutexes projs, doit ienv env p)
      end

  in

  let proc = doit ienv env process in

  (* close the typing environment and substitute *)
  let subst =
    match Infer.close env ienv with        
    | Infer.Closed subst -> subst

    | _ as e ->
      error ~loc:(L.loc process) (Failure (Fmt.str "%a" Infer.pp_error_result e))
  in

  let args = List.map (Subst.subst_var subst) args in
  let proc = gsubst subst proc in

  { args; projs; time; proc; }


(*------------------------------------------------------------------*)
(** {2 Process declarations} *)

(** Declare a new declared process. *)
let declare
    (table : Symbols.table)
    ~(id : lsymb) ~(args : Typing.bnds) ~(projs : lsymb list option)
    (proc : Parse.t)
  =
  let projs = Typing.parse_projs projs in

  (* type-check and declare *)
  let pdecl = parse table ~args projs proc in

  let table = declare_typed table id pdecl in

  (* notify the user of the processus declaration *)
  pp_process_declaration table ~id pdecl;

  table
