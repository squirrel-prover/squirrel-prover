type single_system =
  | Left  of Symbols.system Symbols.t
  | Right of Symbols.system Symbols.t

let get_proj = function
  | Left _ -> Term.Left
  | Right _ -> Term.Right

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
  | Single s -> Fmt.pf fmt "%a" pp_single s
  | SimplePair id -> Fmt.pf fmt "%s/both" (Symbols.to_string id)
  | Pair (s1, s2) ->  Fmt.pf fmt "%a|%a" pp_single s1 pp_single s2

(*------------------------------------------------------------------*)
exception BiSystemError of string

let bisystem_error s = raise (BiSystemError s)

let project_system proj = function
  | Single s -> bisystem_error "cannot project system which \
                                is not a bi-process"
  | SimplePair id ->
    begin
      match proj with
      | Term.Left  -> Single (Left id)
      | Term.Right -> Single (Right id)
      | Term.None  -> bisystem_error "cannot project a system with None"
    end
  | Pair (s1, s2) ->
    begin
      match proj with
      | Term.Left  -> Single s1
      | Term.Right -> Single s2
      | Term.None  -> bisystem_error "cannot project a system with None"
    end


(*------------------------------------------------------------------*)
let make_bi_descr d1 d2 =
  let open Action in
  if d1.input <> d2.input || 
     d1.indices <> d2.indices then
    bisystem_error "cannot merge two actions with disctinct \
                    inputs or indexes";
  let condition =
    let is1,t1 = d1.condition 
    and is2,t2 = d2.condition in
    if is1 <> is2 then
      bisystem_error "cannot merge two actions with disctinct \
                      condtion indexes";
    is1, Term.make_bi_term t1 t2 in
  
  let updates = 
    List.map2 (fun (st1, m1) (st2, m2) ->
        if st1 <> st2 then
          bisystem_error "cannot merge two actions with disctinct \
                          states";
        st1,Term.make_bi_term m1 m2)
      d1.updates d2.updates in

  let output = 
    let c1,m1 = d1.output and c2,m2 = d2.output in
    if c1 <> c2 then
      bisystem_error "cannot merge two actions with disctinct \
                      ouput channels";
    c1, Term.make_bi_term m1 m2 in
  
  { d1 with condition = condition; updates = updates; output = output; }

let descr_of_shape table (se : system_expr) shape =
  let getd s_symb = System.descr_of_shape table s_symb shape in

  match se with
  (* we simply project he description according to the projection *)
  | Single s -> 
    let descr = getd (get_id s) in
    Action.pi_descr (get_proj s) descr

  | SimplePair id ->
    let descr = getd id in
    Action.pi_descr Term.None descr

  (* else we need to obtain the two corresponding set of shapes, project them
     correctly, and combine them into a single term. *)
  | Pair (s1, s2) ->
    let left_a  = getd (get_id s1) in
    let right_a = getd (get_id s2) in
      (* else, we combine both actions together. *)
      make_bi_descr
        (Action.pi_descr (get_proj s1) left_a)
        (Action.pi_descr (get_proj s2) right_a)

let descr_of_action table system a =
  let descr = descr_of_shape system table (Action.get_shape a) in
  (* We know that [descr.action] and [a] have the same shape,
   * but run [same_shape] anyway to obtain the substitution from
   * one to the other. *)
  match Action.same_shape descr.action a with
  | None -> assert false
  | Some subst ->
    Action.subst_descr subst descr

let descrs table se =
  let same_shapes descrs1 descrs2 = 
    System.Msh.for_all (fun shape _ ->
        System.Msh.mem shape descrs2) descrs1 &&
    System.Msh.for_all (fun shape _ ->
        System.Msh.mem shape descrs1) descrs2
  in
  let get_shapes s_symb = 
    let descrs_map = System.descrs table s_symb in
    System.Msh.map (fun _ -> ()) descrs_map
  in

  match se with
  | Pair (s1, s2) ->
    (* we must check that the two systems have the same set of shapes *)
    let left_descrs  = get_shapes (get_id s1) in
    let right_descrs = get_shapes (get_id s2) in
    if not (same_shapes left_descrs right_descrs) then
      bisystem_error "Cannot iter over a bisytem with distinct control flow";
    System.Msh.mapi
      (fun shape () -> descr_of_shape table se shape)
      left_descrs
  | SimplePair id ->
    let fds = get_shapes id in
    System.Msh.mapi
      (fun shape () -> descr_of_shape table se shape)
      fds
  | Single s ->
    (* we must projet before iterating *)
    let sname = get_id s in
    let shapes = get_shapes sname in
    System.Msh.mapi
      (fun shape () -> 
         Action.pi_descr (get_proj s) (
           System.descr_of_shape table sname shape ))
      shapes

let iter_descrs 
    table system 
    (f : Action.descr -> unit) =
  let f _ a = f a in
  System.Msh.iter f (descrs table system)

let fold_descrs 
    (acc : 'a) table system 
    (f : 'a -> Action.descr -> 'a) =
  let f _ a acc = f acc a in
  System.Msh.fold f acc (descrs table system) 

let map_descrs 
    table system 
    (f : Action.descr -> 'a) =
  let m = System.Msh.map f (descrs table system) in
  List.map snd (System.Msh.bindings m)

(*------------------------------------------------------------------*)
exception SystemNotFresh


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

(* Given an original system and a descr substitution, register the new simple
   system obtained from the susbtition. *)
let clone_system_subst table original_system new_system substd =
  let odescrs = descrs table original_system in
  let ndescrs = System.Msh.map (fun _ -> subst substd) odescrs in
  if not (System.is_fresh new_system table) 
  then raise SystemNotFresh
  else
    System.Msh.fold (fun _ d table ->
         let s = Action.get_shape d.Action.action in
         let aname = Action.shape_to_symb table s in
         add_action table new_system s (aname,d)
      ) ndescrs table


let pp_descrs ppf (table, system) =
  Fmt.pf ppf "@[<v 2>Available actions:@;@;";
  iter_descrs table system (fun descr ->
      Fmt.pf ppf "@[<v 0>@[%a@]@;@]@;"
        Action.pp_descr descr) ;
  Fmt.pf ppf "@]%!@."


(*------------------------------------------------------------------*)
(** {2 Parser types } *)

let default_system_name = "default"

type p_single_system =
  | P_Left  of string
  | P_Right of string

type p_system_expr =
  | P_Single     of p_single_system
  | P_SimplePair of string
  | P_Pair       of p_single_system * p_single_system

let parse_single table = function
  | P_Left a  -> Left  (Symbols.System.of_string a table)
  | P_Right a -> Right (Symbols.System.of_string a table)

let parse_se table = function
  | P_Single s       -> Single (parse_single table s)
  | P_SimplePair str -> SimplePair (Symbols.System.of_string str table)
  | P_Pair (a,b)     -> Pair ( parse_single table a, 
                               parse_single table b )

