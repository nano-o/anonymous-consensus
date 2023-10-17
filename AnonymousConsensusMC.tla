----------- MODULE AnonymousConsensusMC ---------------

(***************************************************************************)
(* Here we declare constants and make a few definitions for use in the TLC *)
(* configuration file.                                                     *)
(***************************************************************************)

EXTENDS AnonymousConsensus, TLC

\* The processes:
CONSTANTS p1, p2, p3
P_MC == {p1,p2,p3}
\* The values:
\* CONSTANTS v1, v2, v3
\* V_MC == {v1,v2,v3}
CONSTANTS v1, v2
V_MC == {v1,v2}
\* The registers:
CONSTANTS r1, r2, r3, r4, r5
Rs_MC == {r1,r2,r3,r4,r5}
\* Permutations used for symmetry reduction:
Sym == Permutations(P_MC) \cup Permutations(V_MC) \cup Permutations(Rs_MC)

=======================================================