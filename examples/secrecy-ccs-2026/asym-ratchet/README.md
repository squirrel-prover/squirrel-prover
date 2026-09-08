For ease of verification, the case study is split into several files.

`main.sp` imports everything and performs the full security proof:
it imports all the libraries, and contains the final
PCS and FS theorem statements.

Each file can be opened and executed independently.


## Organization

The structure is as follows:

 - `indices.sp`: Indices axiomatization library - indices used to identify the ratcheting steps are ordered.
 - `DHLib.sp`: Standard DH modeling in Squirrel
 - `model.sp`: Protocol model + Healthy/Sync/Safe predicates
 - `utils.sp`: Simple utility lemmas that do not depend on the protocol 
 - `trace.sp`: Helping lemmas concerning some trace properties
 - `non_collision.sp`: Non-collision lemmas, hash chains do not collide except when synced.
 - `oracles.sp`: Definitions of the oracles used in the secrecy proof 
 - `simulation.sp`: Simulation proof: oracles |> frame 
 - `secrecy_p*.sp`: Secrecy proof: oracles *> secrets 

The bulk of the proof described in Section 5 is in `secrecy_p*.sp`.


## Important Note

The Squirrel files include dependencies in `[admit]` mode. This
enables to quickly run Squirrel on a single file, but requires that
all files are checked independently to ensure soundness.
