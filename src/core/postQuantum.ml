(* TODO: quantum: update this file *)

open Term
open Utils


(* For the top level occurences of quantum typed messages, we do not
   use Occurences, as it would not create distinct occurences for
   several occurences of the same macro at top-level, which we want
   here.

   We simply recurse inside the term under tuple and collecting
   quantum values, not going under function applications.

   This function enables to verify the syntactic condition 3, see mli. 
*)
let rec get_top_level_quantum table acc t =
  match t with
  | App _
  | Name _
  | Macro _
  | Var _
  | Proj _
    ->
    if (HighType.is_classical table (Term.ty t)) then
      (
      Printer.prt `Default "ignoring %a@." Term.pp t;
      acc)
    else  t::acc
  | Let (_,_,t) | Quant (_,_,t) -> get_top_level_quantum table acc t
  | Tuple ts -> List.fold_left (get_top_level_quantum table) acc ts
  | Diff pts ->
    (* FEATURE: Here, we consider the Diff as a tuple, which limits
       the possibilities. Could be generalized to allow for diff over
       quantum values. *)
    begin
      match pts with
        Explicit epts ->
        List.fold_left (fun acc (_, pt) ->
            get_top_level_quantum table acc pt) acc epts
    end
  | Find (_,t1,t2,t3) -> List.fold_left (get_top_level_quantum table) acc [t1;t2;t3] 
  | _ -> acc


(* For the syntactic conditions 1 and 2 (see mli), we build
   occurences with the Occurences module. For direct and indirect
   occurences of quantum values, a quantum relevant occurence is
   either: *)
type qocc =
    QAtt of term
  (* an occurence of a qatt function symbol, which must always be
     unifiable of with a pattern of qatt(qrn tau, frame@tau) . *)       
  | QType of term      
  (* a quantum type under some function symbol, which then must be an
     arugment to a qatt symbol. *)
    


module O = Occurrences

(* We build the relevant module to use the occurence module. *)
module QAttOC : O.OccurrenceContent with type content = qocc
                                          and type data = unit =
struct
  type content = qocc
  type data = unit

      (* The collision formula is a dummy one (but we still need to
         instantiate it so that some occurences are not ignored and
         wrongly considered as subsumed by others. *)
  let collision_formula ~(negate : bool)
      ~(content : content) ~(collision : content) ~(data:unit)
    : Term.term
    =
    let _ = data in
    let _ = collision in
    let _ = negate in
    match content with
      QAtt _ | QType _ ->
      let b_v = Vars.mk (Ident.create "collisionbool") Type.tboolean in
      let b_t = Term.mk_var b_v in      
      b_t
        
  let subst_content sigma x =
    match x with
    | QAtt t -> QAtt (Term.subst sigma t)
    | QType t -> QType (Term.subst sigma t)

  let subst_data _ () = ()

  let pp_content ppe fmt x =
    match x with
    | QAtt t -> Fmt.pf fmt "%a call to qatt" (Term._pp ppe) t
    | QType t -> Fmt.pf fmt "%a quantum type element under a function not qatt" (Term._pp ppe) t
                           
  let pp_data _ppe fmt () : unit =
    Fmt.pf fmt ""
end

module QOC = QAttOC
module QOS = O.MakeSearch (QOC)

let mk_simple_occ = QOS.EO.SO.mk_simple_occ
                      
(**
   A IOS.f_fold_occs function.
    Looks for `qocc` type occurences ina term. 
 *)
let get_qatt_occs
    table
    ~(retry : unit -> QOS.simple_occs)
    ~(rec_call : O.pos_info -> Term.term -> QOS.simple_occs)
    (info:O.pos_info)
    (t:term) 
  : QOS.simple_occs =
  (* handles a few cases, using rec_call_on_subterm for rec calls,
     and calls retry_on_subterm for the rest *)
  match t with

  (* We have a qatt occurence *)
  | App (Fun (f, _), l)
    when f = Symbols.fs_qatt->
    let occs = List.concat_map (rec_call info) (l) in
    (* we add to the end here, it seems to produce goals
       in a more intuitive order *)
    occs @
    [ mk_simple_occ
        ~content:(QAtt t)
        ~collision:(QAtt t)
        ~data:()
        ~vars:info.pi_vars
        ~cond:info.pi_cond
        ~typ:info.pi_occtype
        ~sub:info.pi_subterm
        ~show:Show ] 


  (* A function occurence with a quantum arg, which is not under a
     qatt (as qatt is caught by the previous case. *)
  | App (Fun _, l)
    ->
    let occs = List.concat_map (rec_call info) (l) in    
    (* We collect the quantum typed element of l *)
    let new_elems = List.fold_left
        (fun acc t ->
           if (HighType.is_classical table (Term.ty t)) then
             []
           else
             mk_simple_occ
               ~content:(QType t)
               ~collision:(QType t)
               ~data:()
               ~vars:info.pi_vars
               ~cond:info.pi_cond
               ~typ:info.pi_occtype
               ~sub:info.pi_subterm
               ~show:Show
             :: acc)
        []
        l
    in
    occs @ new_elems
  | _ -> retry ()

(* see mli *)
let check_quantum_simulable
    (context : ProofContext.t)
    (ts:terms)
  =
  
  let table  = context.env.table  in
  let system = context.env.system in


  (* Get all qatt occs of type [qocc]. *)
  let occs1 = 
    QOS.find_all_occurrences ~mode:Any (* ~pp_descr:(Some pp_k) *)
      (get_qatt_occs table) context ts
  in

  (* For each QAtt occurences, we will need to check that it is unifiable with the pattern `qatt(qrn tau, frame@tau)` that we build bellow. *)
  let pat =
    let ts_v = Vars.mk (Ident.create "τ") Type.ttimestamp in
    let ts_t = Term.mk_var ts_v in
    let qrnd_ty = Type.tmeasure_rnd in  
    let qrnd : Term.nsymb = Term.mk_symb Symbols.Quantum.qrnd ~info:() qrnd_ty in
    let qrnd_name = Term.mk_name_with_tuple_args qrnd [ts_t] in
    let frame_ty      = Type.tuple [Type.ttimestamp; Type.tquantum_message; Type.tmessage] in
    let info = Term.macro_info_builtin in  
    let frame  : Term.msymb = Term.mk_symb Symbols.Quantum.frame ~info frame_ty in  
    let qinput =
      Term.mk_fun0
        Symbols.fs_qatt { fty = Symbols.ftype_builtin Symbols.fs_qatt; ty_args = [] }
        [Term.mk_tuple [qrnd_name; Term.mk_macro frame [] (ts_t)]]
    in    
    Term.{
      pat_op_term   = qinput;
      pat_op_params = Params.Open.empty;
      pat_op_vars   = Vars.Tag.local_vars [ts_v]; 
    }
  in

  (* function to test if a [qocc] is valid or invalid *)
  let check_valid_occs1 (occ : QOS.ext_occ) =
    match occ.eo_occ.so_cnt with
    | QAtt t ->
      begin
        match Match.T.try_match ~param:Match.crypto_param table system t pat with
        | Match _ ->
          Printer.prt `Default "Good qatt occ: %a @." Term.pp t;
          true
        | NoMatch _ ->          
          Printer.prt `Default "Bad qatt occ not of the form `qatt(qrn \
                                tau, frame@tau)`: %a @." Term.pp t;
          false
      end
    | QType t ->
      Printer.prt `Default "Bad quantum typed value not under a qatt: %a @." Term.pp t;
      false
  in

  if not(List.for_all check_valid_occs1 occs1) then
    (* We instantly fail *)
    false
  else
    (* Otherwise, we then check top level occurences of quantum values. *) 
      let occs2 =
        List.fold_left (get_top_level_quantum table) [] ts
      in

      if List.length occs2 <= 1 then
        (List.iter
           (fun t -> Printer.prt `Default "Valid single top level \
                                           quantum typed value: %a @." Term.pp t) occs2;  
         true)
      else
        (Printer.prt `Default "Invalid sequence, several top level values of quantum type.@.";
         List.iter (fun occ ->
             Printer.prt `Default "Bad quantum typed value: %a @." Term.pp occ)
           occs2;
         false)
