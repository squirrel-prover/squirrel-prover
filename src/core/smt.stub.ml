let[@warning "-27"] literals_unsat ~slow table system evars msg_atoms trace_lits axioms =
  print_endline "smt tactic unavailable:";
  print_endline "Squirrel was compiled without the Why3 API support";
  print_endline "(the why3 package may be missing from your setup)";
  false
