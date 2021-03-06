module L = Location

type lsymb = Symbols.lsymb

(*------------------------------------------------------------------*)
type single_system =
  | Left  of Symbols.system Symbols.t
  | Right of Symbols.system Symbols.t

let get_proj = function
  | Left _ -> Term.PLeft
  | Right _ -> Term.PRight

let get_id = function
  | Left id | Right id -> id

(*------------------------------------------------------------------*)
type system_expr =
  | Single     of single_system
  | SimplePair of Symbols.system Symbols.t
  | Pair       of single_system * single_system

let pp_single fmt = function
  | Left id  -> Fmt.pf fmt "%s/left"  (Symbols.to_string id)
  | Right id -> Fmt.pf fmt "%s/right" (Symbols.to_string id)

let pp_system fmt = function
  | Single s      -> Fmt.pf fmt "%a" pp_single s
  | SimplePair id -> Fmt.pf fmt "%s/both" (Symbols.to_string id)
  | Pair (s1, s2) -> Fmt.pf fmt "%a|%a" pp_single s1 pp_single s2

(*------------------------------------------------------------------*)
type ssymb_pair = System.system_name * 
                  System.system_name

type system_expr_err = 
  | SE_NotABiProcess of System.system_name
  | SE_NoneProject
  | SE_IncompatibleAction   of ssymb_pair * string
  | SE_DifferentControlFlow of ssymb_pair

let pp_system_expr_err fmt = function
  | SE_NotABiProcess s -> 
    Fmt.pf fmt "cannot project system [%s], which is not a bi-process"
      (Symbols.to_string s)

  | SE_NoneProject -> 
    Fmt.pf fmt "cannot project a system with None"

  | SE_IncompatibleAction ((s1,s2),s) ->
    Fmt.pf fmt "systems [%s] and [%s] are not compatible: %s" 
      (Symbols.to_string s1) (Symbols.to_string s2) s
      
  | SE_DifferentControlFlow (s1,s2) ->
    Fmt.pf fmt "systems [%s] and [%s] have distinct control flow" 
      (Symbols.to_string s1) (Symbols.to_string s2) 

exception BiSystemError of system_expr_err

let bisystem_error e = raise (BiSystemError e)

let incompatible_error s1 s2 s = 
  raise (BiSystemError (SE_IncompatibleAction ((s1,s2),s)))

(*------------------------------------------------------------------*)
let project_system proj = function
  | Single s -> bisystem_error (SE_NotABiProcess (get_id s))

  | SimplePair id ->
    begin
      match proj with
      | Term.PLeft  -> Single (Left id)
      | Term.PRight -> Single (Right id)
      | Term.PNone  -> bisystem_error SE_NoneProject
    end
  | Pair (s1, s2) ->
    begin
      match proj with
      | Term.PLeft  -> Single s1
      | Term.PRight -> Single s2
      | Term.PNone  -> bisystem_error SE_NoneProject
    end

(*------------------------------------------------------------------*)
let make_bi_descr s1 s2 d1 d2 =
  let incompatible s = incompatible_error s1 s2 s in

  let open Action in
  if not ( d1.name = d2.name ) then
    incompatible "cannot merge two actions with disctinct names";

  if not ( d1.input = d2.input ) then
    incompatible "cannot merge two actions with disctinct inputs";

  if not ( d1.indices = d2.indices ) then
    incompatible "cannot merge two actions with disctinct indices";

  if Action.same_shape d1.action d2.action = None then 
    incompatible "cannot merge two actions with different shapes";

  let condition =
    let is1,t1 = d1.condition 
    and is2,t2 = d2.condition in
    if is1 <> is2 then
      incompatible "cannot merge two actions with disctinct \
                    condition indexes";
    is1, Term.make_bi_term t1 t2 in
  
  let updates = 
    List.map2 (fun (st1, m1) (st2, m2) ->
        if st1 <> st2 then
          incompatible "cannot merge two actions with disctinct \
                        states";
        st1,Term.make_bi_term m1 m2)
      d1.updates d2.updates in

  let output = 
    let c1,m1 = d1.output and c2,m2 = d2.output in
    if c1 <> c2 then
      incompatible "cannot merge two actions with disctinct \
                    ouput channels";
    c1, Term.make_bi_term m1 m2 in

  { name = d1.name;
    action = d1.action;
    input = d1.input;
    indices = d1.indices; 
    condition = condition; 
    updates = updates; 
    output = output; }

let descr_of_shape table (se : system_expr) shape =
  let getd s_symb = System.descr_of_shape table s_symb shape in

  match se with
  (* we simply project the description according to the projection *)
  | Single s ->
    let descr = getd (get_id s) in
    Action.pi_descr (get_proj s) descr

  | SimplePair id ->
    let descr = getd id in
    Action.pi_descr Term.PNone descr

  (* else we need to obtain the two corresponding sets of shapes,
     project them correctly, and combine them into a single term. *)
  | Pair (s1, s2) ->
    let sname1 = get_id s1 in
    let sname2 = get_id s2 in
    let left_a  = getd sname1 in
    let right_a = getd sname2 in
    make_bi_descr sname1 sname2
      (Action.pi_descr (get_proj s1) left_a)
      (Action.pi_descr (get_proj s2) right_a)

let descr_of_action table (system : system_expr) a =
  let descr = descr_of_shape table system (Action.get_shape a) in
  (* We know that [descr.action] and [a] have the same shape,
   * but run [same_shape] anyway to obtain the substitution from
   * one to the other. *)
  match Action.same_shape descr.action a with
  | None -> assert false
  | Some subst ->
    Action.subst_descr subst descr

let descrs table se = 
  let same_shapes descrs1 descrs2 = 
    System.Msh.for_all (fun shape d1 ->
        System.Msh.mem shape descrs2) descrs1 &&
    System.Msh.for_all (fun shape _ ->
        System.Msh.mem shape descrs1) descrs2
  in

  (* We built the new action descriptions *)
  match se with
  | Pair (s1, s2) ->
    (* we must check that the two systems have the same set of shapes *)
    let sname1 = get_id s1
    and sname2 = get_id s2 in
    let left_descrs  = System.descrs table sname1 in
    let right_descrs = System.descrs table sname2 in
    if not (same_shapes left_descrs right_descrs) then
      bisystem_error (SE_DifferentControlFlow (sname1,sname2));
    System.Msh.mapi
      (fun shape _ -> descr_of_shape table se shape)
      left_descrs
  | SimplePair id ->
    let fds = System.descrs table id in
    System.Msh.mapi
      (fun shape descr -> Action.pi_descr Term.PNone descr)
      fds
  | Single s ->
    (* we must projet before iterating *)
    let sname = get_id s in
    let shapes = System.descrs table sname in
    System.Msh.mapi
      (fun shape descr -> Action.pi_descr (get_proj s) descr)
      shapes

let iter_descrs 
    table system 
    (f : Action.descr -> unit) =
  let f _ a = f a in
  System.Msh.iter f (descrs table system)

let map_descrs 
    table system 
    (f : Action.descr -> 'a) =
  let m = System.Msh.map f (descrs table system) in
  List.map snd (System.Msh.bindings m)


(** Check that a system expression is valid. This is not obvious only 
    in the [Pair _] case, in which case we check that the two single 
    systems are compatible. *)
let check_system_expr table se = iter_descrs table se (fun _ -> ())
(* computing the system description has the side-effect of checking that 
   the systems are compatible *)

(*------------------------------------------------------------------*)
(** {2 Smart constructor } *)

let single _table a = Single a

let simple_pair _table s = SimplePair s

(* This is the only case where we have to check that the system are 
   compatible. *)
let pair table a b =  
  let se = Pair(a,b) in
  check_system_expr table se; se

(*------------------------------------------------------------------*)

(** Get the action symbols table of a system expression.
  * We rely on the invariant that the system systems involved in an expression
  * must have the same such table. *)
let symbs table = function
  | SimplePair s | Pair (Left s,_) | Pair (Right s,_)
  | Single (Left s) | Single (Right s) -> System.symbs table s

let action_to_term table system a =
  let symbs = symbs table system in
  let symb = System.Msh.find (Action.get_shape a) symbs in
    Term.Action (symb, Action.get_indices a)

(*------------------------------------------------------------------*)

(** A substition over a description that allows to either substitute the condition
   or the output of the descr, for a given shape. *)
type esubst_descr =
  | Condition of Term.formula * Action.action
  | Output of Term.message * Action.action

type subst_descr = esubst_descr list

let rec subst s d =
  match s with
  | [] -> d
  | Condition (f,a) :: q ->
    begin
      match Action.same_shape a d.Action.action with
      | None -> subst q d
      | Some s ->
          subst q {d with condition = (fst(d.condition), Term.subst s f)}
    end
  | Output (t,a) :: q ->
    begin
      match Action.same_shape a d.Action.action with
      | None -> subst q d
      | Some s ->
          subst q {d with output = (fst(d.output), Term.subst s t)}
    end

exception SystemNotFresh

(* Given an original system and a descr substitution, register the new simple
   system obtained from the susbtition. *)
(* let clone_system_subst table original_system new_system substd =
 *   let odescrs = descrs table original_system in
 *   let symbs = symbs table original_system in
 *   let ndescrs = System.Msh.map (subst substd) odescrs in
 *   let data = System.System_data (ndescrs,symbs) in
 *   Symbols.System.declare_exact table new_system ~data ()  *)

let pp_descrs table ppf system =
  Fmt.pf ppf "@[<v 2>Available actions:@;@;";
  iter_descrs table system (fun descr ->
      Fmt.pf ppf "@[<v 0>@[%a@]@;@]@;"
        Action.pp_descr descr) ;
  Fmt.pf ppf "@]%!@."


(*------------------------------------------------------------------*)
(** {2 Parser types } *)

let default_system_name = L.mk_loc Location._dummy "default"

type p_single_system =
  | P_Left  of lsymb
  | P_Right of lsymb

type p_system_expr =
  | P_Single     of p_single_system
  | P_SimplePair of lsymb
  | P_Pair       of p_single_system * p_single_system

let pp_p_single fmt = function
  | P_Left id  -> Fmt.pf fmt "%s/left"  (L.unloc id)
  | P_Right id -> Fmt.pf fmt "%s/right" (L.unloc id)

let pp_p_system fmt = function
  | P_Single s      -> Fmt.pf fmt "%a" pp_p_single s
  | P_SimplePair id -> Fmt.pf fmt "%s/both" (L.unloc id)
  | P_Pair (s1, s2) -> Fmt.pf fmt "%a|%a" pp_p_single s1 pp_p_single s2

let parse_single table = function
  | P_Left a  -> Left  (System.of_lsymb a table)
  | P_Right a -> Right (System.of_lsymb a table)

let parse_se table p_se = match p_se with
    | P_Single s       -> single table (parse_single table s)
    | P_SimplePair str -> simple_pair table (System.of_lsymb str table)
    | P_Pair (a,b)     -> 
      pair table (parse_single table a) (parse_single table b) 
