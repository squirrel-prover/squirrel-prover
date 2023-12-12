open Squirrelcore
module ES   = EquivSequent
module Args = HighTacticsArgs
module LT   = LowTactics
  
(*------------------------------------------------------------------*)
val case_tac        : Args.parser_args -> LT.etac
val fa_tac          : Args.parser_args -> LT.etac 
val assumption_tac  : Args.parser_args -> LT.etac 
val constraints_tac : Args.parser_args -> LT.etac

val old_or_new_induction : Args.parser_args -> LT.etac

val equiv_autosimpl : LT.gentac

val equiv_auto :
  red_param:Reduction.red_param ->
  close:bool ->
  strong:bool -> LT.gentac
