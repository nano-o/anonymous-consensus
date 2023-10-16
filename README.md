This repository contains a TLA+ formalization of the fully anonymous, obstruction-free set-consensus algorithm of Raynal and Taubenfeld.
See [AnonymousConsensus.tla](./AnonymousConsensus.tla).

The algorithm appears in: Raynal and Taubenfeld, *Fully anonymous consensus and set agreement algorithms*, NETYS 2020.

We check with the TLC model-checker that this algorithm violates consensus when there are 3 processors and 5 registers.
The counter-example run appears in [AnonymousConsensusMC.out](./AnonymousConsensusMC.out).
TLC found it in 12 minutes on a recent desktop computer.
