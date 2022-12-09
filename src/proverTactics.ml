type tactic_groups =
  | Logical
  (** Sequence calculus logical properties. *)

  | Structural
  (** Properties inherent to protocol, on equality between messages, behaviour 
     of if _ then _ else _, action dependencies... *)

  | Cryptographic
  (** Cryptographic assumptions. *)

(** The record for a detailed help tactic. *)
type tactic_help = { general_help  : string;
                     detailed_help : string;
                     usages_sorts  : TacticsArgs.esort list;
                     tactic_group  : tactic_groups;
                   }

type 'a tac_infos = {
  maker    : TacticsArgs.parser_arg list -> 'a Tactics.tac ;
  pq_sound : bool;
  help     : tactic_help ;
}

type 'a table = (string, 'a tac_infos) Hashtbl.t

(*------------- Basic Tactic tables, without registration-----------*)(* {↓{ *)
(** Basic tactic tables, without registration *)

module TacTable : sig
  val table : Goal.t table
  val tac_count_table : (string, int) Hashtbl.t

  val get : bool -> Location.t -> string -> TacticsArgs.parser_arg list -> Goal.t Tactics.tac
  val add_tac : string -> Goal.t tac_infos -> unit

  val pp_goal_concl : Format.formatter -> Goal.t -> unit
end = struct
  let table = Hashtbl.create 97
  let tac_count_table = Hashtbl.create 97

  let add_tac (id:string) (tacinfo:Goal.t tac_infos) =
    Hashtbl.add tac_count_table id 0;
    Hashtbl.add table id tacinfo

  let get (post_quantum:bool) loc id =
    try let tac = Hashtbl.find table id in
      if not(tac.pq_sound) && post_quantum then
        Tactics.hard_failure Tactics.TacticNotPQSound
      else
        let count = Hashtbl.find tac_count_table id in
        Hashtbl.replace tac_count_table id (count+1);
        tac.maker
    with
      | Not_found -> Tactics.hard_failure ~loc
             (Tactics.Failure (Printf.sprintf "unknown tactic %S" id))

  let pp_goal_concl ppf j = match j with
    | Goal.Trace j -> Term.pp  ppf (LowTraceSequent.goal j)
    | Goal.Equiv j -> Equiv.pp ppf (LowEquivSequent.goal j)
end
(* }↑} *)

(** AST evaluators for general judgment. *)(* {↓{ *)
module AST :
  (Tactics.AST_sig
   with type arg = TacticsArgs.parser_arg
   with type judgment = Goal.t)
= Tactics.AST(struct

  type arg = TacticsArgs.parser_arg

  type judgment = Goal.t

  let pp_arg = TacticsArgs.pp_parser_arg

  let autosimpl () = TacTable.get false Location._dummy "autosimpl" []
  let autosimpl = Lazy.from_fun autosimpl

  let re_raise_tac loc tac s sk fk : Tactics.a =
    try tac s sk fk with
    | Tactics.Tactic_hard_failure (None, e) -> Tactics.hard_failure ~loc e
    | Tactics.Tactic_soft_failure (None, e) -> Tactics.soft_failure ~loc e

  let eval_abstract post_quantum mods (id : Theory.lsymb) args : judgment Tactics.tac =
    let loc, id = Location.loc id, Location.unloc id in
    let tac = re_raise_tac loc (TacTable.get post_quantum loc id args) in
    match mods with
      | "nosimpl" :: _ -> tac
      | [] -> Tactics.andthen tac (Lazy.force autosimpl)
      | _ -> assert false
end)
(* }↑} *)

let pp_ast fmt t = AST.pp fmt t

(*-------- ProverTactics --------------------------------------*)(* {↓{ *)
let dbg s = Printer.prt (if Config.debug_tactics () then `Dbg else `Ignore) s

let bad_args () = Tactics.hard_failure (Failure "improper arguments")

(* ProverTactics *)(* {↓{ *)
include TacTable

type judgment = Goal.t

type tac = judgment Tactics.tac

let register_general id ~tactic_help ?(pq_sound=false) f =
  let () = assert (not (Hashtbl.mem table id)) in

  let f args s sk fk =
    dbg "@[<hov>calling tactic %s on@ @[%a@]@]"
      id TacTable.pp_goal_concl s;
    f args s sk fk
  in

  add_tac id { maker = f ;
               help = tactic_help;
               pq_sound}

let convert_args j parser_args tactic_type =
  let env, conc =
    match j with
    | Goal.Trace t -> LowTraceSequent.env t, Equiv.Local (LowTraceSequent.goal t)

    | Goal.Equiv e -> 
      LowEquivSequent.env e, Equiv.Global (LowEquivSequent.goal e)
  in
  HighTacticsArgs.convert_args env parser_args tactic_type conc

let register id ~tactic_help ?(pq_sound=false) f =
  register_general id ~tactic_help ~pq_sound
    (function
      | [] ->
        fun s sk fk -> begin match f s with
            | subgoals -> sk subgoals fk
            | exception Tactics.Tactic_soft_failure e -> fk e
          end
      | _ -> Tactics.hard_failure (Tactics.Failure "no argument allowed"))

let register_typed id
    ~general_help ~detailed_help
    ~tactic_group ?(pq_sound=false) ?(usages_sorts)
    f sort =
  let usages_sorts = match usages_sorts with
    | None -> [TacticsArgs.Sort sort]
    | Some u -> u in

  register_general id
    ~tactic_help:({general_help; detailed_help; usages_sorts; tactic_group})
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

(* FIXME never used ? *)
(* let register_macro *)
(*       id ?(modifiers=["nosimpl"]) ~tactic_help ?(pq_sound=false) m = *)
(*   register_general id ~tactic_help ~pq_sound *)
(*     (fun args s sk fk -> *)
(*        if args = [] then AST.eval false modifiers m s sk fk else *)
(*          Tactics.hard_failure *)
(*            (Tactics.Failure "this tactic does not take arguments")) *)

let pp_usage tacname fmt esort =
  Fmt.pf fmt "%s %a" tacname TacticsArgs.pp_esort esort
let pp details fmt (id : Theory.lsymb) =
  let id_u = Location.unloc id in
  let help =
    try (Hashtbl.find table id_u).help with
    | Not_found -> Tactics.hard_failure ~loc:(Location.loc id)
        (Tactics.Failure (Printf.sprintf "unknown tactic %S" id_u))
  in
  Fmt.pf fmt  "@.@[- %a -@\n @[<hov 3>   %a @\n %a @\n%s @[%a @] @]@]@."
    (fun ppf s -> Printer.kw `HelpFunction ppf "%s" s)
    id_u
    Format.pp_print_text
    help.general_help
    Format.pp_print_text
    (if details && help.detailed_help <> "" then
       "\n" ^ help.detailed_help ^ "\n" else "")
    (if List.length help.usages_sorts = 0 then ""
     else if List.length help.usages_sorts =1 then "Usage:"
     else "Usages:")
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf "@\n") (pp_usage id_u))
    help.usages_sorts

let pps fmt () =
  let helps =
    Hashtbl.fold (fun name tac acc -> (name, tac.help)::acc) table []
    |> List.sort (fun (n1,_) (n2,_) -> compare n1 n2)
  in
  Fmt.pf fmt "%a" Format.pp_print_text
    "List of all tactics with short description.\n \
     `help tacname` gives more details about a tactic. \n\
     `help concise` juste gives the list of tactics. \n\
      Tactics are organized in three categories: \n \
     - logical, that rely on logical properties of the sequence;\n - \
     structural, that rely on properties of protocols and equality;\n - \
     cryptographic, that rely on some cryptographic assumption that must be \
     explicitly stated.\n";
  let filter_cat helps cat =
    List.filter (fun (_,x) -> x.tactic_group = cat) helps
  in
  let str_cat = function
    | Logical -> "Logical"
    | Structural -> "Structural"
    | Cryptographic -> "Cryptographic"
  in
  List.iter (fun cat ->
      Printer.kw `HelpType fmt "\n%s"
        (str_cat cat^" tactics:");
      List.iter (fun (name, help) ->
          if help.general_help <> "" then
            Fmt.pf fmt "%a" (pp false) (Location.mk_loc Location._dummy name)
        ) (filter_cat helps cat)
  )
  [Logical; Structural; Cryptographic]

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
  Printf.fprintf oc "}\n"

let pp_list fmt () =
  let helps =
    Hashtbl.fold (fun name tac acc -> (name, tac.help)::acc) table []
    |> List.sort (fun (n1,_) (n2,_) -> compare n1 n2)
  in
  let filter_cat helps cat = List.filter (fun (_,x) -> x.tactic_group = cat) helps in
  let str_cat = function
    | Logical -> "Logical"
    | Structural -> "Structural"
    | Cryptographic -> "Cryptographic"
  in
  List.iter (fun cat ->
      Printer.kw `HelpType fmt "\n%s"
        (str_cat cat^" tactics:\n");
      Fmt.pf fmt "%a"
        (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf "; ")
           (fun ppf (name,_) ->
              Printer.kw `HelpFunction ppf "%s" name))
        (filter_cat helps cat);
    )
    [Logical; Structural; Cryptographic]
(* }↑} *)

let get_help (tac_name : Theory.lsymb) =
  if Location.unloc tac_name = "" then
    Printer.prt `Result "%a" pps ()
  else if Location.unloc tac_name = "concise" then
    Printer.prt `Result "%a" pp_list ()
  else
    Printer.prt `Result "%a" (pp true) tac_name;
  Tactics.id
(* }↑} *)

(*-------- Declare Tactics here ! TOMOVE ! TODO ---------------*)(* {↓{ *)
let () =
  register_general "lemmas"
    ~tactic_help:{general_help = "Print all proved lemmas.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    ~pq_sound:true
    (fun _ s sk fk ->
       let table = Goal.table s in
       Printer.prt `Result "%a" Lemma.print_all table;
       sk [s] fk)

let () =
  register_general "prof"
    ~tactic_help:{general_help = "Print profiling information.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    ~pq_sound:true
    (fun _ s sk fk ->
       Printer.prt `Dbg "%a" Prof.print ();
       sk [s] fk)

let () =
  register_general "help"
    ~tactic_help:{general_help = "Display all available commands.\n\n\
                                  Usages: help\n\
                                 \        help tacname\n\
                                 \        help concise";
                  detailed_help = "`help tacname` gives more details about a \
                                   tactic and `help concise` juste gives the \
                                   list of tactics.";
                  usages_sorts = [];
                  tactic_group = Logical}
    ~pq_sound:true
    (function
      | [] -> get_help (Location.mk_loc Location._dummy "")
      | [String_name tac_name]-> get_help tac_name
      | _ ->  bad_args ())

let () =
  register_general "id"
    ~tactic_help:{general_help = "Identity.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    ~pq_sound:true
    (fun _ -> Tactics.id)
(* }↑} *)
