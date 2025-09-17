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

(*********************************)
(* OLD PQ tests to be deprecated *)
(*********************************)


(** Verification of the syntactic conditions
    required for post-quantum soundness. 

We rely on the theory from SP'22:
    C. Cremers, C. Fontaine, and C. Jacomme, “A Logic and an Interactive Prover for the Computational Post-Quantum Security of Protocols,” in Proceedings of the 43nd IEEE Symposium on Security and Privacy (S&P’22), 2022, https://hal.inria.fr/hal-03620358.

In general, there are three conditions to checks on goals in the BC logic, assuming that all attacker calls are lists (nested tuples), and can thus be seen as att(t1,...,tn):
 * consistency: all occurences of att symbol with the same arity have exactly the same inputs
 * monotonicity: all inputs of att symbols form a growing list of inputs (prefix ordering)
 * balance: for an equivalence, the attacker is called as many times on both sides

Consistency and monotonicity are trivially implied if all occurences of the att function symbol (which did not exist in Squirrel at the time of SP'22 paper) are of the form att(frame@t).
This check is performed in the `check_att` function below, that needs to be called for both equivalence and reachability goals.


A balance check is needed for equivalence. The simplest sufficient condition is to find on both side the maximal timestamp, and check that for this maximal timestamp T,  input@T occurs on both sides.
We currently rely on Lemma 9 of SP'22 to have this check go through more often by checking alternative side-conditions covering other occurences of frame/output. 

Alternatively, we could avoid relying on Lemma 9, which may break with updates of the prover/logic, but change the macro definition of the frame macro in the pq setting so that input is included inside of it. This would however imply that a lot of exisiting proofs would break, and especially, turning an existing proof into a PQ one would now take way more work, while it is mostly free currently.

TOCHECK: If equivalence of the form frame^P@T, frame^Q@T become allowed, additional checks for the PQ soundness will be needed.

TODO: call check_att for reachability goals

*)



(** Sets of terms, intended to store timestamps. *)
module Sts = Set.Make (Term)

(** Sets of terms, intended to store macros. *)
module Stt = Set.Make (Term)  


class collect_max_ts ~(context:ProofContext.t) = object (self)
  (* We fold over the terms, collecting all the timestamps, and maintaining a
     list of timestamps that are smaller than another timestamp. *)
  (* TODO: remove deprecated fold *)
  inherit [Sts.t * Sts.t] Iter.deprecated_fold ~context as super

  method extract_ts_atoms phi =
    List.partition (fun t ->
        let at = Term.Lit.form_to_xatom t in
        Term.Lit.ty_xatom at = Type.ttimestamp
      ) (Term.decompose_ands phi)

  (* Given a set of atoms, returns a list of ts that are smaller than other
     timestamps. *)
  method add_atoms atoms  =
    List.fold_left
      (fun smaller_acc at ->
         match Term.Lit.form_to_xatom at with
         | Comp (`Leq,tau_1,_tau_2) ->
           (* TODO: [tau_2] unused, is it normal? This works only if tau_2 is in max_att *)
           Sts.add tau_1 smaller_acc
         | Comp (`Lt,tau_1,_tau_2) ->
           (* TODO: [tau_2] unused, is it normal? *)
           Sts.add tau_1 smaller_acc
        | _ -> smaller_acc)
      Sts.empty
      atoms

  (* We collect all the macro timestamps occurring inside terms, that are not
     explicitly smaller than other timestamps. *)
  method fold_message (max_ts,ignore_ts) t = match t with

    (* We ignore timestamps explicitly smaller than others. *)
    | Macro (_ms,[],a) when Sts.mem a ignore_ts -> (max_ts,ignore_ts)

    (* We don't care about input macros. *)
    (* TODO: why? equiv(diff(input@t1, input@t2)) is clearly not syncrhonized *)
    | Macro (ms,[],_a) when ms.s_symb = Symbols.Classic.inp -> (max_ts,ignore_ts)

    (* For other macros, we add the ts to the possible max_ts, but we don't
       unfold the macro, as it would only contain smaller timestamps. *)
    | Macro (_,_, ts) -> (Sts.add ts max_ts, ignore_ts)

    (* If we consider an implication, we can collect from the lhs which ts we
       can ignore in the rhs. *)
    | App (Fun (f, _), [phi_1;phi_2]) when f = Term.f_impl ->
      let atoms,l = self#extract_ts_atoms phi_1 in
      let ignore_ts' = Sts.union (self#add_atoms atoms) ignore_ts  in
      List.fold_left
        (fun acc phi -> self#fold_message acc phi)
        (max_ts,ignore_ts')
        (phi_2::l)

    (* We proceed similarly for conjunctions. *)
    | App (Fun (f, _), _) when f = Term.f_and ->
      let atoms,l = self#extract_ts_atoms t in
      let ignore_ts' = Sts.union (self#add_atoms atoms) ignore_ts  in
      List.fold_left
        (fun acc phi -> self#fold_message acc phi)
        (max_ts,ignore_ts')
        l
    | _ -> super#fold_message (max_ts,ignore_ts) t

end

class collect_macros ~(context:ProofContext.t) = object (_self)

  (* TODO: drop deprecated *)
  inherit [Stt.t] Iter.deprecated_fold ~context as super

  (* We collect all the macros occurring inside terms, that are not under
     a diff. *)
  method fold_message acc t = match t with
    | Macro (_ms,[],_a) as m -> Stt.add m acc
    | Diff _ -> acc
    | _ -> super#fold_message acc t

end



class check_att ~(context:ProofContext.t) = object (self)
  (* we check that all occurences of the att symbol are of the form
     att(frame@T), and thus in fact correspond to an input. *)
  (* TODO: drop deprecated *)                                                     
  inherit [bool] Iter.deprecated_fold ~context as super

  method fold_message aux t = match t with
    (* TODO: quantum: new symbol is [fs_qatt] *)
    | App (Fun (sf, _), [Macro (ms,_,_)]) when sf = Symbols.fs_att ->
      ms.s_symb = Symbols.Classic.frame && aux
    (* we accept att(frame@t) *)
    (* TODO: quantum: new symbol is [fs_qatt] *)
    | App (Fun (sf, _), _) when sf = Symbols.fs_att -> false
    (* we reject any other att(x) *)
    | Macro _ ->
      let res, has_red =
        Match.reduce_delta_macro1
          ~constr:true
          context.env ~hyps:context.hyps t
      in
      if has_red = True then self#fold_message aux res else true
    | _ -> super#fold_message aux t

end


let is_attacker_call_synchronized context models biframe =
  let iter_att = new check_att ~context in
  let check_att =
    List.fold_left
      (fun acc t -> iter_att#fold_message true t && acc)
      true
      biframe
  in
  if not check_att then false else
    let (max_ts, _) =
      let iter = new collect_max_ts ~context in
      List.fold_left
        (fun (max_ts,_) t-> iter#fold_message (max_ts, Sts.empty) t)
        (Sts.empty, Sts.empty) biframe
    in
    let maximal_elems =
      Sts.filter (function
        | App (Term.Fun (fs, _), [ts]) when fs = Term.f_pred ->
          (* Directly remove pred(t) with t in the set. *)
          (* TODO: This is probably useless, check if improves perfs? *)
          not (Sts.mem ts max_ts)
        | _ -> true
      ) max_ts
    in
    let maximal_elems =
      Constr.maximal_elems ~precise:false models (Sts.elements maximal_elems)
    in
    let macros =
      let iter = new collect_macros ~context in
      List.fold_left (fun acc t-> iter#fold_message acc t)
        Stt.empty biframe
    in
    let has_frame_or_input tau =
      let frame_at t =
        Term.mk_macro Macros.Classic.frame [] t
      in
      let frame_at_pred t =
        Term.mk_macro Macros.Classic.frame [] (Term.mk_pred t)
      in
      let input_at t =
        Term.mk_macro Macros.Classic.inp [] t
      in
      let ok_list =
        [frame_at tau; frame_at_pred tau; input_at tau]
        @
        match tau with
        | Term.App (Fun (fs, _), [tau']) when fs = Term.f_pred ->
          [frame_at tau'; frame_at_pred tau'; input_at tau']
        | _ -> []
      in
      not @@ Stt.is_empty @@ Stt.inter (Stt.of_list ok_list) macros
    in
    List.for_all (fun tau -> has_frame_or_input tau) maximal_elems
