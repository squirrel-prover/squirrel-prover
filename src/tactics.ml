
exception Tactic_Hard_Failure of string

type tac_error =
  | Failure of string
  | AndThen_Failure of tac_error

let rec pp_tac_error ppf = function
  | Failure s -> Fmt.pf ppf "%s" s
  | AndThen_Failure t ->
      Fmt.pf ppf
        "An application of the second tactic to one \
         of the subgoal failed with error : %a"
        pp_tac_error t

type a

type fk = tac_error -> a

type 'a sk = 'a -> fk -> a

type 'a tac = 'a -> 'a list sk -> fk -> a

(** Basic Tactics *)

let fail sk fk = fk (Failure "fail")

let wrap f v sk fk = sk (f v) fk

let return a v = a v (fun r fk' -> r) (fun _ -> raise @@ Failure "return")

(** [map t [e1;..;eN]] returns all possible lists [l1@..@lN]
  * where [li] is a result of [t e1]. *)
let map t l sk fk =
  let rec aux acc l sk fk = match l with
    | [] -> sk (List.rev acc) fk
    | e::l ->
        t e
          (fun r fk ->
             aux (List.rev_append r acc) l sk fk)
          fk
  in aux [] l sk fk

let orelse_nojudgment a b sk fk = a sk (fun tac_error -> b sk fk)

let orelse a b j sk fk = orelse_nojudgment (a j) (b j) sk fk

let orelse_list l j =
  List.fold_right (fun t t' -> orelse_nojudgment (t j) t') l fail

let andthen tac1 tac2 judge sk fk =
  tac1 judge
    (fun l fk -> map tac2 l sk fk)
    fk

let rec andthen_list = function
  | [] -> raise (Tactic_Hard_Failure "empty anthen_list")
  | [t] -> t
  | t::l -> andthen t (andthen_list l)

let id j sk fk = sk [j] fk

let try_tac t = orelse t id

let repeat t j sk fk =
  let rec aux j sk fk =
    t j
      (fun l fk -> map aux l sk fk)
      (fun e -> sk [j] fk)
  in aux j sk fk

(** Generic tactic syntax trees *)

module type S = sig

  type arg
  val pp_arg : Format.formatter -> arg -> unit

  type judgment

  val eval_abstract : string -> arg list -> judgment tac
  val pp_abstract : pp_args:(Format.formatter -> arg list -> unit) ->
    string -> arg list -> Format.formatter -> unit

end

module type AST_sig = sig

  type arg
  type judgment

  (** AST for tactics, with abstract leaves corresponding to prover-specific
    * tactics, with prover-specific arguments. Modifiers have no internal
    * semantics: they are printed, but ignored during evaluation -- they
    * can only be used for cheap tricks now, but may be used to guide tactic
    * evaluation in richer ways in the future. *)
  type t =
    | Abstract of string * arg list
    | AndThen : t list -> t
    | OrElse : t list -> t
    | Try : t -> t
    | Repeat : t -> t
    | Ident : t
    | Modifier : string * t -> t

  val eval : t -> judgment tac

  val pp : Format.formatter -> t -> unit

end

module AST (M:S) = struct

  open M

  (** AST for tactics, with abstract leaves corresponding to prover-specific
    * tactics, with prover-specific arguments. *)
  type t =
    | Abstract of string * arg list
    | AndThen : t list -> t
    | OrElse : t list -> t
    | Try : t -> t
    | Repeat : t -> t
    | Ident : t
    | Modifier : string * t -> t

  type arg = M.arg
  type judgment = M.judgment

  let rec eval = function
    | Abstract (id,args) -> eval_abstract id args
    | AndThen tl -> andthen_list (List.map eval tl)
    | OrElse tl -> orelse_list (List.map eval tl)
    | Try t -> try_tac (eval t)
    | Repeat t -> repeat (eval t)
    | Ident -> id
    | Modifier (id,t) -> eval t

  let pp_args fmt l =
    Fmt.list
      ~sep:(fun ppf () -> Fmt.string ppf ",@ ")
      pp_arg fmt l

  let rec pp ppf = function
    | Abstract (i,args) ->
        begin try
          pp_abstract ~pp_args i args ppf
        with _ ->
          if args = [] then Fmt.string ppf i else
            Fmt.pf ppf "%s %a" i pp_args args
        end
    | Modifier (i,t) -> Fmt.pf ppf "%s(%a)" i pp t
    | AndThen [t;t'] ->
        Fmt.pf ppf "@[%a@]; @,@[%a@]" pp t pp t'
    | OrElse [t;t'] ->
        Fmt.pf ppf "@[%a@] + @,@[%a@]" pp t pp t'
    | AndThen _ | OrElse _ -> assert false (* TODO *)
    | Ident -> Fmt.pf ppf "id"
    | Try t ->
        Fmt.pf ppf "try @[%a@]" pp t
    | Repeat t ->
        Fmt.pf ppf "repeat @[%a@]" pp t

end
