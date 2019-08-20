open Action
(** Terms and formulas for the Meta-BC logic.
  *
  * This modules describes the syntax of the logic. It does not
  * provide low-level representations, normal forms, etc. that
  * are to be used in automated reasoning, nor does it provide
  * representations necessary for the front-end involving
  * processes, axioms, etc. *)

(** Timestamps represent positions in a trace *)

type tvar = Tvar_i of int

let pp_tvar ppf = function Tvar_i i -> Fmt.pf ppf "ts%d" i

let tvar_cpt = ref 0
let fresh_tvar () = incr tvar_cpt; Tvar_i (!tvar_cpt - 1)

type timestamp =
  | TVar of tvar
  | TPred of timestamp
  | TName of action

let rec pp_timestamp ppf = function
  | TVar tv -> pp_tvar ppf tv
  | TPred ts -> Fmt.pf ppf "@[<hov>p(%a)@]" pp_timestamp ts
  | TName a -> Action.pp_action ppf a

(** Names represent random values, uniformly sampled by the process.
  * A name symbol is derived from a name (from a finite set) and
  * a list of indices. *)

type name = Name of string

(* TODO declarations, freshness conditions ? *)
let mk_name x = Name x
let fresh_name x = Name x

let pp_name ppf = function Name s -> (Utils.kw `Yellow) ppf ("n!"^s)

type nsymb = name * indices

let pp_nsymb ppf (n,is) =
  if is <> [] then Fmt.pf ppf "%a[%a]" pp_name n pp_indices is
  else Fmt.pf ppf "%a" pp_name n

(** Function symbols are built from a name (from a finite set)
  * and a list of indices.
  *
  * TODO must include builtins such as if-then-else, equality, successor, xor ...
  * Adrien: already added some
  * Some keywords should probably be forbidden, e.g. "input", "output"
  *)

type fname = Fname of string

let pp_fname ppf = function Fname s -> (Utils.kw `Bold) ppf s

type fsymb = fname * indices

let pp_fsymb ppf (fn,is) = match is with
  | [] -> Fmt.pf ppf "%a" pp_fname fn
  | _ -> Fmt.pf ppf "%a[%a]" pp_fname fn pp_indices is

let mk_fname f = (Fname f, [])
let mk_fname_idx f l = (Fname f, l)

(** Boolean function symbols *)
let f_false = (Fname "false", [])
let f_true = (Fname "true", [])
let f_and = (Fname "and", [])
let f_or = (Fname "or", [])
let f_not = (Fname "not", [])

(** IfThenElse function symbol *)
let f_ite = (Fname "if", [])

(** Xor function symbol *)
let f_xor = (Fname "xor", [])

(** Zero function symbol. Satisfies 0 + a -> a *)
let f_zero = (Fname "zero", [])

(** Successor function symbol *)
let f_succ = (Fname "succ", [])

(** Memory cells are represented by state variable, themselves
  * derived from a name (from a finite set) and indices.
  *
  * TODO simplify design to merge name, function and state names ?
  *)

type sname = Sname of string
let mk_sname x = Sname x

let pp_sname ppf = function Sname s -> (Utils.kw `Red) ppf ("s!"^s)

type state = sname * indices

let pp_state ppf (sn,is) =
  if is <> [] then Fmt.pf ppf "%a(%a)" pp_sname sn pp_indices is
  else Fmt.pf ppf "%a" pp_sname sn

(** Type of macros name *)
type mname = string
type msymb = mname * indices

let pp_mname ppf s =
  let open Fmt in
  (styled `Bold (styled `Magenta Utils.ident)) ppf ("m!"^s)

let pp_msymb ppf (m,is) =
  Fmt.pf ppf "%a%a"
    pp_mname m
    (Utils.pp_ne_list "(%a)" pp_indices) is

(** Terms *)
type term =
  | Fun of fsymb * term list
  | Name of nsymb
  | State of state * timestamp
  (* | Input of timestamp *)
  | Macro of msymb * timestamp

let dummy = Fun ((Fname "_",[]),[])

let rec pp_term ppf = function
  | Fun (f,terms) ->
      Fmt.pf ppf "%a%a"
        pp_fsymb f
        (Utils.pp_ne_list
           "(@[<hov>%a@])"
           (Fmt.list ~sep:Fmt.comma pp_term)) terms
  | Name n -> pp_nsymb ppf n
  | State (s,ts) -> Fmt.pf ppf "@[%a@%a@]" pp_state s pp_timestamp ts
  | Macro (m,ts) -> Fmt.pf ppf "@[%a@%a@]" pp_msymb m pp_timestamp ts
  (* | Input ts -> Fmt.pf ppf "@[in@%a@]" pp_timestamp ts *)

type t = term

let macros : (string, (timestamp -> indices -> term)) Hashtbl.t =
  Hashtbl.create 97

let built_ins = ["input";"output"]

(** [is_built_in mn] returns true iff [mn] is a built-in.  *)
let is_built_in mn = List.mem mn built_ins

let is_declared mn =
  if Hashtbl.mem macros mn || List.mem mn built_ins then mn
  else raise Not_found

let declare_macro mn f =
  assert (not (is_built_in mn) && not (Hashtbl.mem macros mn)) ;
  Hashtbl.add macros mn f;
  mn                            (* TODO: refresh if already there *)


(** Return the term corresponding to the declared macro, except for the
    built-ins "input" and "output". *)
let macro_declaration mn =
  if is_built_in mn then
    raise @@ Failure "look-up of a built-in declaration"
  else Hashtbl.find macros mn

let mk_mname mn indices = (mn,indices)

let in_macro = ("input",[])
let out_macro = ("output",[])

(** Boolean formulas *)
type 'a bformula =
  | And of 'a bformula * 'a bformula
  | Or of 'a bformula * 'a bformula
  | Not of 'a bformula
  | Impl of 'a bformula * 'a bformula
  | Atom of 'a
  | True
  | False

let rec pp_bformula pp_atom ppf = function
  | And (bl,br) ->
    Fmt.pf ppf "@[<hv>(%a && %a)@]"
      (pp_bformula pp_atom) bl (pp_bformula pp_atom) br
  | Or (bl,br) ->
    Fmt.pf ppf "@[<hv>(%a || %a)@]"
      (pp_bformula pp_atom) bl (pp_bformula pp_atom) br
  | Impl (bl,br) ->
    Fmt.pf ppf "@[<hv>(%a -> %a)@]"
      (pp_bformula pp_atom) bl (pp_bformula pp_atom) br
  | Not b ->
    Fmt.pf ppf "@[<hv>not(%a)@]" (pp_bformula pp_atom) b
  | Atom a -> pp_atom ppf a
  | True -> Fmt.pf ppf "true"
  | False -> Fmt.pf ppf "false"

(** [atoms b] returns the list of atoms appearing in [b] *)
let atoms b =
  let rec aux acc = function
    | True | False -> acc
    | And (a,b) | Or (a,b) | Impl (a,b) -> aux (aux acc a) b
    | Not a -> aux acc a
    | Atom at -> at :: acc in

  aux [] b



(** Evaluate trivial subformula. *)
let rec triv_eval = function
  | Or (a,b) ->
    begin match triv_eval a, triv_eval b with
      | _, True | True,_ -> True
      | _ as te, False | False, (_ as te) -> te
      | _ as ta, (_ as tb) -> Or (ta, tb) end

  | And (a,b) ->
    begin match triv_eval a, triv_eval b with
      | _ as te, True | True, (_ as te) -> te
      | _, False | False,_ -> False
      | _ as ta, (_ as tb) -> And (ta, tb) end

  | Impl (a,b) ->
    begin match triv_eval a, triv_eval b with
      | _, True | False, _ -> True
      | True, (_ as te) -> te
      | _ as ta, (_ as tb) -> Impl (ta, tb) end

  | Not a -> begin match triv_eval a with
      | True -> False
      | False -> True
      | _ as ta -> Not ta end

  | _ as a -> a

(** [simpl_formula nlit b] simplifies the bformula [b], using [nlit] to
    transform negative atoms into positive atoms *)
let simpl_formula nlit b =
  let rec simp flip = function
    | Atom a -> if flip then Atom (nlit a) else Atom a
    | True -> if flip then False else True
    | False -> if flip then True else False
    | Or (l,r) ->
      if flip then And (simp flip l, simp flip r)
      else Or (simp flip l, simp flip r)
    | And (l,r) ->
      if flip then Or (simp flip l, simp flip r)
      else And (simp flip l, simp flip r)
    | Impl (l,r) ->  Or (Not l, r) |> simp flip
    | Not b -> simp (not flip) b in
  simp false b |> triv_eval


(** [bf_dnf nlit b] puts the  bformula [b] in DNF, using [nlit] to transform
    negative atoms into positive atoms *)
let bf_dnf : ('a -> 'a) -> 'a bformula -> 'a list list = fun nlit b ->

  let rec dnf = function
    | Or (a,b) -> dnf a @ dnf b
    | False -> []
    | True -> [[]]
    | Atom a -> [[a]]
    | And (a,b) ->
      let bdnf = dnf b in
      List.fold_left (fun acc c ->
          (List.fold_left (fun acc c' ->
               (c @ c') :: acc) acc bdnf))
        [] (dnf a)
    | Impl _ | Not _ -> assert false in

  simpl_formula nlit b |> dnf


(** Atoms *)

type ord = Eq | Neq | Leq | Geq | Lt | Gt

type 'a _atom = ord * 'a * 'a

type atom = term _atom

type fact = atom bformula

let pp_ord ppf = function
  | Eq -> Fmt.pf ppf "="
  | Neq -> Fmt.pf ppf "<>"
  | Leq -> Fmt.pf ppf "<="
  | Geq -> Fmt.pf ppf ">="
  | Lt -> Fmt.pf ppf "<"
  | Gt -> Fmt.pf ppf ">"

let not_ord o = match o with
  | Eq -> Neq
  | Neq -> Eq
  | Leq -> Gt
  | Geq -> Lt
  | Lt -> Geq
  | Gt -> Leq

let pp_atom ppf (o,tl,tr) =
    Fmt.pf ppf "@[<h>%a %a %a@]" pp_term tl pp_ord o pp_term tr

let pp_fact = pp_bformula pp_atom

(** Negate the atom *)
let not_xpred (o,l,r) = (not_ord o, l, r)

let simpl_fact f = simpl_formula not_xpred f

(** Replace an atom by an equivalent list of atoms using only Eq,Neq and Leq *)
let norm_xatom (o,l,r) = match o with
  | Eq | Neq | Leq -> [(o,l,r)]
  | Geq -> [(Leq,r,l)]
  | Lt -> (Leq,l,r) :: [(Neq,l,r)]
  | Gt -> (Leq,r,l) :: [(Neq,r,l)]

let add_xeq od xeq (eqs,leqs,neqs) = match od with
  | Eq -> (xeq :: eqs, leqs, neqs)
  | Leq -> (eqs, xeq :: leqs, neqs)
  | Neq -> (eqs, leqs, xeq :: neqs)
  | _ -> raise (Failure ("add_xeq: bad comparison operator"))


(** Constraints:
    - [Pind (o,i,i')] : [o] must be either [Eq] or [Neq] *)
type tatom =
  | Pts of timestamp _atom
  | Pind of index _atom

type constr = tatom bformula

let pts (o,t,t') = Pts (o,t,t')
let pind (o,i,i') = Pind (o,i,i')

let pp_tatom ppf = function
  | Pts (o,tl,tr) ->
    Fmt.pf ppf "@[<h>%a %a %a@]" pp_timestamp tl pp_ord o pp_timestamp tr
  | Pind (o,il,ir) ->
    Fmt.pf ppf "@[<h>%a %a %a@]" pp_index il pp_ord o pp_index ir

let not_tpred = function
  | Pts (o,t,t') -> pts (not_xpred (o,t,t'))
  | Pind (o,i,i') -> pind (not_xpred (o,i,i'))

let norm_tatom = function
  | Pts (o,t,t') -> norm_xatom (o,t,t') |> List.map pts
  | Pind _ as x -> [x]

let pp_constr ppf = pp_bformula pp_tatom ppf

(** Put a constraint in DNF using only atoms Eq, Neq and Leq *)
let constr_dnf (c : constr) =
  bf_dnf not_tpred c
  |> List.map (fun l -> List.map norm_tatom l
                        |> List.flatten)



(** Correspondence formulas *)


(** A formula is always of the form
  *   forall [uvars,uindices] such that [uconstr],
  *   [ufact] => [postcond],
  * with a postcondition that is a disjunction
  * of formulas of the form
  *   exists [evars,eindices] such that [econstr] and [efact]. *)
type formula = {
  uvars : tvar list;
  uindices : indices;
  uconstr : constr;
  ufact : fact;
  postcond : postcond list
}
and postcond = {
  evars : tvar list;
  eindices : indices;
  econstr : constr;
  efact : fact
}

let pp_q_vars s_q vars indices constr ppf () =
  let open Fmt in
  let open Utils in
  if vars <> [] then
    Fmt.pf ppf "@[<hv 2>%a@ (@[<hov>%a@] : %a)@]@;"
     (styled `Red (styled `Underline ident)) s_q
     (list ~sep:Fmt.comma pp_tvar) vars
     (styled `Blue (styled `Bold ident)) "timestamp"
  else ();
  if indices <> [] then
    Fmt.pf ppf "@[<hv 2>%a@ (@[<hov>%a@] : %a)@]@;"
     (styled `Red (styled `Underline ident)) s_q
     pp_indices indices
     (styled `Blue (styled `Bold ident)) "index"
  else ();
  if constr <> True then
    Fmt.pf ppf "@[<hv 2>%a@ @[<hov>%a@]@]@;"
     (styled `Red (styled `Underline ident)) "such that"
     pp_constr constr
  else ();;

let pp_postcond ppf f =
  Fmt.pf ppf "@[<v 0>%a%a@]"
    (pp_q_vars "exists" f.evars f.eindices f.econstr) ()
    pp_fact f.efact

let pp_precond ppf f =
  Fmt.pf ppf "@[<v 0>%a%a@]"
    (pp_q_vars "forall" f.uvars f.uindices f.uconstr) ()
    pp_fact f.ufact

let pp_formula ppf f =
  let open Fmt in
  let open Utils in
  match f.postcond with
  | [] -> pp_precond ppf f
  | [a] ->
    Fmt.pf ppf "@[<v 0>%a@;%a %a@]"
      pp_precond f
      (styled `Red (styled `Underline ident)) "=>"
      pp_postcond a
  | a :: l ->
    Fmt.pf ppf "@[<v 0>%a@;%a %a%a@]"
      pp_precond f
      (styled `Red (styled `Underline ident)) "=>"
      pp_postcond a
      (list
         ~sep:(fun ppf () ->
             Fmt.pf ppf "%a "
             (styled `Red (styled `Underline ident)) "@;\\/")
         pp_postcond) l


let ivar_subst_symb isubst (fn, is) = (fn, List.map (app_subst isubst) is)

let ivar_subst_state isubst (s : state) = ivar_subst_symb isubst s

let rec tvar_subst_ts tsubst ts = match ts with
  | TVar tv -> TVar (app_subst tsubst tv)
  | TPred ts' -> TPred (tvar_subst_ts tsubst ts')
  | TName _ -> ts

let rec ivar_subst_ts isubst = function
  | TVar _ as ts -> ts
  | TPred ts' -> TPred (ivar_subst_ts isubst ts')
  | TName a -> TName (ivar_subst_action isubst a)

let rec tvar_subst_term tsubst t = match t with
  | Fun (fs, lt) -> Fun (fs, List.map (tvar_subst_term tsubst) lt)
  | Name _ -> t
  | State (s, ts) -> State (s, tvar_subst_ts tsubst ts)
  | Macro (m,ts) -> Macro (m,tvar_subst_ts tsubst ts)
  (* | Input ts -> Input (tvar_subst_ts tsubst ts) *)

let rec ivar_subst_term isubst t = match t with
  | Fun (fs, lt) -> Fun ( ivar_subst_symb isubst fs,
                          List.map (ivar_subst_term isubst) lt )
  | Name n -> Name (ivar_subst_symb isubst n)
  | State (s, ts) -> State ( ivar_subst_symb isubst s,
                             ivar_subst_ts isubst ts )
  | Macro (m,ts) -> Macro (m,ivar_subst_ts isubst ts)
  (* | Input ts -> Input (ivar_subst_ts isubst ts) *)

let subst_term isubst tsubst m = ivar_subst_term isubst m
                                 |> tvar_subst_term tsubst

let rec var_subst_form at_subst subst f = match f with
  | And (a,b) -> And ( var_subst_form at_subst subst a,
                       var_subst_form at_subst subst b )
  | Or (a,b) -> Or ( var_subst_form at_subst subst a,
                     var_subst_form at_subst subst b )
  | Impl (a,b) -> Impl ( var_subst_form at_subst subst a,
                         var_subst_form at_subst subst b )
  | Not a -> Not (var_subst_form at_subst subst a)
  | Atom at -> Atom (at_subst subst at)
  | True | False -> f

let tvar_subst_atom subst (ord,t,t') =
  (ord, tvar_subst_term subst t, tvar_subst_term subst t')

let ivar_subst_atom isubst (ord,t,t') =
  (ord, ivar_subst_term isubst t, ivar_subst_term isubst t')

let tvar_subst_fact = var_subst_form tvar_subst_atom

let ivar_subst_fact = var_subst_form ivar_subst_atom

let subst_fact isubst tsubst m = ivar_subst_fact isubst m
                                 |> tvar_subst_fact tsubst

let tvar_subst_tatom subst = function
  | Pts (ord, ts, ts') ->
    Pts (ord, tvar_subst_ts subst ts, tvar_subst_ts subst ts')
  | Pind _ as at -> at

let ivar_subst_tatom isubst = function
  | Pts (ord, ts, ts') ->
    Pts (ord, ivar_subst_ts isubst ts, ivar_subst_ts isubst ts')
  | Pind (ord, i, i') -> Pind (ord, app_subst isubst i, app_subst isubst i')

let tvar_subst_constr = var_subst_form tvar_subst_tatom

let ivar_subst_constr = var_subst_form ivar_subst_tatom

let subst_constr isubst tsubst m = ivar_subst_constr isubst m
                                   |> tvar_subst_constr tsubst


(** Timestamp variables substitution in a post-condition.
    Pre-condition: [tvar_subst_postcond subst pc] require that [subst]
    co-domain is fresh in [pc]. *)
let tvar_subst_postcond subst pc =
  let subst = List.filter (fun (v,_) -> not @@ List.mem v pc.evars) subst in
  { pc with econstr = tvar_subst_constr subst pc.econstr;
            efact = tvar_subst_fact subst pc.efact }

(** Index variables substitution in a post-condition.
    Pre-condition: [ivar_subst_postcond isubst pc] require that [isubst]
    co-domain is fresh in [pc]. *)
let ivar_subst_postcond subst pc =
  let subst = List.filter (fun (v,_) -> not @@ List.mem v pc.eindices) subst in
  { pc with econstr = ivar_subst_constr subst pc.econstr;
            efact = ivar_subst_fact subst pc.efact }

(** Substitution in a post-condition.
    Pre-condition: [subst_postcond isubst tsubst pc] require that [isubst]
    and [tsubst] co-domains are fresh in [pc]. *)
let subst_postcond isubst tsubst m = ivar_subst_postcond isubst m
                                     |> tvar_subst_postcond tsubst

let svars (tvs,ivs) (_, is) =
  (tvs, is @ ivs)

let rec tsvars (tvs,ivs) = function
  | TVar tv -> (tv :: tvs, ivs)
  | TName a -> (tvs, action_indices a @ ivs)
  | TPred ts -> tsvars (tvs,ivs) ts

let rec tvars acc = function
  | Fun (fs, lt) -> List.fold_left tvars (svars acc fs) lt
  | Name n -> svars acc n
  | State (s, ts) -> tsvars (svars acc s) ts
  (* | Input ts *)
  | Macro (_,ts) -> tsvars acc ts

(** [term_vars t] returns the timestamp and index variables of [t]*)
let term_vars t =
  let tvs, ivs = tvars ([],[]) t in
  ( List.sort_uniq Pervasives.compare tvs,
    List.sort_uniq Pervasives.compare ivs )

(** [tss_vars tss] returns the timestamp and index variables of [tss]*)
let tss_vars tss =
  let tvs, ivs = List.fold_left tsvars ([],[]) tss in
  ( List.sort_uniq Pervasives.compare tvs,
    List.sort_uniq Pervasives.compare ivs )


let rec tts acc = function
  | Fun (fs, lt) -> List.fold_left tts acc lt
  | Name n -> acc
  | State (_, ts)
  (* | Input ts *)
  | Macro (_,ts) -> ts :: acc

(** [term_ts t] returns the timestamps appearing in [t] *)
let term_ts t = tts [] t |> List.sort_uniq Pervasives.compare

let rec atsts acc = function
  | [] -> acc
  | (_,t,t') :: l -> atsts (tts (tts acc t) t') l

(** [atoms_ts ats] returns the timestamps appearing in [ats] *)
let atoms_ts at = atsts [] at |> List.sort_uniq Pervasives.compare

let rec tatsts acc = function
  | [] -> acc
  | (Pind _) :: l -> tatsts acc l
  | (Pts (_,ts,ts')) :: l -> tatsts (ts :: ts' :: acc) l

let f_fts f_at acc fact =
  let rec fts acc = function
  | True | False -> acc
  | And (a,b) | Or (a,b) | Impl (a,b) -> fts (fts acc a) b
  | Not a -> fts acc a
  | Atom at -> f_at acc at in

  fts acc fact

(** [fact_ts f] returns the timestamps appearing in [f] *)
let fact_ts f = f_fts (fun acc x -> atsts acc [x]) [] f

(** [constr_ts c] returns the timestamps appearing in [c] *)
let constr_ts c = f_fts (fun acc x -> tatsts acc [x]) [] c
