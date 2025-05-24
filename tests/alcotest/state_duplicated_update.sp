(* Translation is expected to fail on system below,
   due to the two updates on s.

   The expected failure does not happen with a replication,
   because the updates (and output) are in conflict and thus the
   action is split in several actions, with at most one update in each one.
   The issue appears again with replication and with a mutex.

   Translation may be refined in the future to handle multiple updates
   on the same cell in a block, but the current setup cannot handle it. *)

abstract n0 : message
abstract v : message

mutable s : message = n0

channel c

system
  in(c,x);
  s := <s,x>;
  s := s;
  out(c,s).
