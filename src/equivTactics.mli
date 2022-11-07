module ES   = EquivSequent
module Args = HighTacticsArgs
module LT   = LowTactics
  
(*------------------------------------------------------------------*)
val case_tac        : Args.parser_args -> LT.etac 
val fa_tac          : Args.parser_args -> LT.etac 
val assumption_tac  : Args.parser_args -> LT.etac 
val constraints_tac : Args.parser_args -> LT.etac

val old_or_new_induction : Args.parser_args -> LT.etac

val tac_autosimpl : Args.parser_args -> LT.gentac

val tac_auto :
  red_param:Reduction.red_param ->
  close:bool ->
  strong:bool -> Args.parser_args -> LT.gentac
