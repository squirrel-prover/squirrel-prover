(*------------------------------------------------------------------*)
(** {3 Discriminate (equality, disequality)} 

    This code is used to check that the cases of a pattern-match
    are mutually exclusive, and to implement the `discriminate`
    tactic. *)

(*------------------------------------------------------------------*)
(** try to reduce the left or right term *)
let try_reduce
    (red_state : Reduction.state Lazy.t) (l : Term.t) (r : Term.t)
  : (Term.t * Term.t, unit) Result.t
  =
  let l, has_red = Reduction.whnf_term ~strat:Std (Lazy.force red_state) l in
  if has_red then Result.Ok (l, r)
  else
    let r, has_red = Reduction.whnf_term ~strat:Std (Lazy.force red_state) r in
    if has_red then Result.Ok (l, r)
    else Result.Error ()

(*------------------------------------------------------------------*)
(** Exported, see `.mli` *)
let discriminate_eq
    (red_state : Reduction.state Lazy.t)
    (table : Symbols.table)
    (l : Term.t) (r : Term.t) : bool
  =
  let rec discriminate_eq (l : Term.t) (r : Term.t) : [`Eq | `Neq | `Unknown] =
    match Term.decompose_app l, Term.decompose_app r with
    | (Int i, []), (Int j,[]) -> if Z.equal i j then `Eq else `Neq
    | (String l,[]), (String r,[]) -> if String.equal l r then `Eq else `Neq

    | (Fun (fsl, ftyl), argsl),
      (Fun (fsr, ftyr), argsr) ->
      begin
        match Symbols.OpData.constructor_of fsl table,
              Symbols.OpData.constructor_of fsr table with
        | Some cl, Some cr ->
          assert (Symbols.path_equal cl cr);
          if Symbols.path_equal fsl fsr &&
             List.for_all2 Type.equal ftyl.ty_args ftyr.ty_args then
            (* same constructor on both side,
               look for a diverging constructor below a shared constructor *)
            discriminate_eq_list argsl argsr

          (* we found an equality between different constructors *)
          else `Neq
        | _ -> try_reduce_eq l r 
      end

    (* look for a diverging constructor below a tuple *)
    | (Tuple l, []), (Tuple r, []) -> discriminate_eq_list l r

    | _ -> try_reduce_eq l r 

  and try_reduce_eq (l : Term.t) (r : Term.t) : [`Eq | `Neq | `Unknown] =
    match try_reduce red_state l r with
    | Result.Error () -> `Unknown
    | Result.Ok (l,r) -> discriminate_eq l r

  and discriminate_eq_list
      (l : Term.t list) (r : Term.t list) : [`Eq | `Neq | `Unknown]
    =
    let has_unknown = ref false in
    let has_neq     = ref false in
    List.iter2 (fun tl tr ->
        match discriminate_eq tl tr with
        | `Neq -> has_neq := true
        | `Unknown -> has_unknown := true
        | `Eq -> ()
      ) l r;
    if not !has_neq && not !has_unknown then `Eq else
    if !has_neq then `Neq
    else `Unknown
  in
  discriminate_eq l r = `Neq

(*------------------------------------------------------------------*)
(** Check if [l] is a subterm of [r] *)
let rec find_subterm (l : Term.t) (r : Term.t) : bool =
  Term.equal l r ||
  Term.texists (find_subterm l) r

(*------------------------------------------------------------------*)
(** Exported, see `.mli` *)
let discriminate_lt
    (red_state : Reduction.state Lazy.t)
    (table : Symbols.table)
    ~(large : bool) (l : Term.t) (r : Term.t) : bool
  =
  let exception Failed in

  (** - [true] means ([l < r] if [not large], and [l ≤ r] if [large]), 
      - [false] mean [l = r]
        Raise [Failed] if we do not manage to compare [l] and [r]. *)
  let rec doit ?(large : bool = false) (l : Term.t) (r : Term.t) : bool =
    if large && Term.equal l r then true else
      match r,l with
      | Int r, Int l -> Z.lt l r
      | String r, String l -> 
        String.compare l r < 0

      | App (Fun (fsr, _), argsr),_ ->
        begin
          match Symbols.OpData.constructor_of fsr table with
          | Some _ ->
            List.exists (find_subterm l) argsr ||
            doit_rec l r
          | _ -> try_reduce_doit ~large l r
        end

      | Tuple argsr,_ ->
        List.exists (find_subterm l) argsr ||
        doit_rec l r

      | _ ->
        if Term.equal l r then false
        else try_reduce_doit ~large l r

  and try_reduce_doit ~(large:bool) (l : Term.t) (r : Term.t) : bool =
    match try_reduce red_state l r with
    | Result.Error () -> raise Failed
    | Result.Ok (l,r) -> doit ~large l r

  (** try to recurse below [l] and [r] if they starts with a
      common top-level constructors, and show that [l < r] *)
  and doit_rec (l : Term.t) (r : Term.t) : bool =
    match l, r with
    | App (Fun (fsl, ftyl), argsl),
      App (Fun (fsr, ftyr), argsr) ->
      begin
        match Symbols.OpData.constructor_of fsl table,
              Symbols.OpData.constructor_of fsr table with
        | Some cl, Some cr ->
          assert (Symbols.path_equal cl cr);
          if Symbols.path_equal fsl fsr &&
             List.for_all2 Type.equal ftyl.ty_args ftyr.ty_args then
            (* same constructor on both side,
               recurse in lexicographic ordering *)
            List.exists2 doit argsl argsr

          (* We found an inequality between different constructors,
             we do not know how to recurse. *)
          else raise Failed
        | _ -> try_reduce_doit_rec l r
      end

    (* recurse below a tuple, in lexicographic order *)
    | Tuple l, Tuple r -> List.exists2 doit l r

    | _ -> try_reduce_doit_rec l r

  and try_reduce_doit_rec (l : Term.t) (r : Term.t) : bool =
    match try_reduce red_state l r with
    | Result.Error () -> raise Failed
    | Result.Ok (l,r) -> doit_rec l r

  in
  try doit ~large l r with Failed -> false
