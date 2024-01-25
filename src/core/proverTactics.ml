type 'a tac_infos = {
  maker    : TacticsArgs.parser_arg list -> 'a Tactics.tac ;
  pq_sound : bool;
}

type 'a table = (string, 'a tac_infos) Hashtbl.t

(** Basic tactic tables, without registration. *)
module TacTable : sig
  val table : Goal.t table
  val tac_count_table : (string, int) Hashtbl.t

  val get :
    post_quantum:bool -> loc:Location.t ->
    string -> TacticsArgs.parser_arg list ->
    Goal.t Tactics.tac

  val add_tac : string -> Goal.t tac_infos -> unit

  val pp_goal_concl : Format.formatter -> Goal.t -> unit
end = struct
  let table = Hashtbl.create 97
  let tac_count_table = Hashtbl.create 97

  let add_tac (id:string) (tacinfo:Goal.t tac_infos) =
    Hashtbl.add tac_count_table id 0;
    Hashtbl.add table id tacinfo

  let get ~post_quantum ~loc id =
    try let tac = Hashtbl.find table id in
      if not tac.pq_sound && post_quantum then
        Tactics.hard_failure Tactics.TacticNotPQSound
      else
        let count = Hashtbl.find tac_count_table id in
        Hashtbl.replace tac_count_table id (count+1);
        tac.maker
    with
      | Not_found -> Tactics.hard_failure ~loc
             (Tactics.Failure (Printf.sprintf "unknown tactic %S" id))

  let pp_goal_concl ppf j = match j with
    | Goal.Local  j -> Term.pp  ppf (LowTraceSequent.conclusion j)
    | Goal.Global j -> Equiv.pp ppf (LowEquivSequent.conclusion j)
end

(** AST evaluators for general judgments, i.e. [Goal.t]. *)
module AST :
  (Tactics.AST_sig
   with type arg = TacticsArgs.parser_arg
   with type judgment = Goal.t)
= Tactics.AST(struct

  type arg = TacticsArgs.parser_arg
  type judgment = Goal.t

  let pp_arg = TacticsArgs.pp_parser_arg

  let autosimpl () = TacTable.get ~post_quantum:false ~loc:Location._dummy "autosimpl" []
  let autosimpl = Lazy.from_fun autosimpl

  let re_raise_tac loc tac s sk fk : Tactics.a =
    try tac s sk fk with
    | Tactics.Tactic_hard_failure (None, e) -> Tactics.hard_failure ~loc e
    | Tactics.Tactic_soft_failure (None, e) -> Tactics.soft_failure ~loc e

  let eval_abstract ~post_quantum ~modifiers id args =
    let loc, id = Location.loc id, Location.unloc id in
    let tac = re_raise_tac loc (TacTable.get ~post_quantum ~loc id args) in
    match modifiers with
      | "nosimpl" :: _ -> tac
      | [] -> Tactics.andthen tac (Lazy.force autosimpl)
      | _ -> assert false

end)

(* ----------------------------------------------------------------------- *)

let dbg s = Printer.prt (if Config.debug_tactics () then `Dbg else `Ignore) s

let bad_args () = Tactics.hard_failure (Failure "improper arguments")

include TacTable

type judgment = Goal.t

type tac = judgment Tactics.tac

let register_general id ?(pq_sound=false) f =
  let () = assert (not (Hashtbl.mem table id)) in

  let f args s sk fk =
    dbg "@[<hov>calling tactic %s on@ @[%a@]@]"
      id TacTable.pp_goal_concl s;
    f args s sk fk
  in

  add_tac id { maker = f ; pq_sound }

let register_macro id ast =
  register_general id
    (fun args ->
      if args <> [] then
        let msg =
          Format.sprintf "tactic %S does not accept any argument." id in
        Tactics.(hard_failure (Failure msg))
      else
        AST.eval ~post_quantum:true ~modifiers:[] ast)

let convert_args j parser_args tactic_type =
  let env, conc =
    match j with
    | Goal.Local t ->
      LowTraceSequent.env t, Equiv.Local (LowTraceSequent.conclusion t)
    | Goal.Global e ->
      LowEquivSequent.env e, Equiv.Global (LowEquivSequent.conclusion e)
  in
  HighTacticsArgs.convert_args env parser_args tactic_type conc

let register id ?(pq_sound=false) f =
  register_general id ~pq_sound
    (function
      | [] ->
        fun s sk fk -> begin match f s with
            | subgoals -> sk subgoals fk
            | exception Tactics.Tactic_soft_failure e -> fk e
          end
      | _ -> Tactics.hard_failure (Tactics.Failure "no argument allowed"))

let register_typed id ?(pq_sound=false) f sort =
  register_general id
    ~pq_sound
    (fun args s sk fk ->
       match convert_args s args (TacticsArgs.Sort sort) with
       | TacticsArgs.Arg th  ->
         try
           let th = TacticsArgs.cast sort th in
           begin
             match f th s with
             | subgoals -> sk subgoals fk
             | exception Tactics.Tactic_soft_failure e -> fk e
           end
         with TacticsArgs.Uncastable ->
           Tactics.hard_failure (Tactics.Failure "ill-formed arguments"))

let pp_list_count (file:string) : unit =
  let oc = open_out file in
  let counts =
    Hashtbl.fold (fun name count acc -> (name, count)::acc) tac_count_table []
    |> List.sort (fun (n1,_) (n2,_) -> compare n1 n2)
  in
  Printf.fprintf oc "{\n";
  List.iteri (fun i (name,count) ->
    if i < (List.length counts)-1 then
      Printf.fprintf oc "\"%s\" : %d, \n" name count
    else
      Printf.fprintf oc "\"%s\" : %d \n" name count
  ) counts;
  Printf.fprintf oc "}\n";
  Stdlib.close_out_noerr oc
(*-------- Declare Tactics here ! TODO move as commands ---------------*)
let () =
  register_general "lemmas"
    ~pq_sound:true
    (fun _ s sk fk ->
       let table = Goal.table s in
       Printer.prt `Result "%a" Lemma.print_all table;
       sk [s] fk)

let () =
  register_general "id"
    ~pq_sound:true
    (fun _ -> Tactics.id)
