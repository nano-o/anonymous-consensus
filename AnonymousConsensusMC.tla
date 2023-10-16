----------- MODULE AnonymousConsensusMC ---------------

EXTENDS AnonymousConsensus, TLC

CONSTANTS p1, p2, p3
P_MC == {p1,p2,p3}
CONSTANTS r1, r2, r3, r4, r5
Rs_MC == {r1,r2,r3,r4,r5}
Sym == Permutations(P_MC) \cup Permutations(V) \cup Permutations(Rs)

=======================================================