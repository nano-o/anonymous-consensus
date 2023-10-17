This repository contains a TLA+ formalization of the fully anonymous, obstruction-free set-consensus algorithm of Raynal and Taubenfeld.
The algorithm appears in: Raynal and Taubenfeld, *Fully anonymous consensus and set agreement algorithms*, NETYS 2020.

The formalization is in [AnonymousConsensus.tla](./AnonymousConsensus.tla).
[AnonymousConsensusMC.tla](./AnonymousConsensusMC.tla) and [AnonymousConsensusMC.cfg](./AnonymousConsensusMC.cfg) are used to configure the TLC model-checker.

We check with the TLC model-checker that this algorithm violates agreement (this is expected and shown in the paper) when there are 3 processors and 5 registers.
The counter-example run appears in [ConsensusViolation.out](./ConsensusViolation.out).

Even though the counter-example run is 97 steps long, TLC found it in only 12 minutes on a recent desktop computer.
The key to efficient model-checking is to realize that, in this anonymous model, symmetry reduction can be applied not only to process ids and values but also to register names.

[AnonymousConsensusMC.out](./AnonymousConsensusMC.out) contains the TLC output log when checking the set-consensus property for 3 processes, 5 registers, and 3 values.
It took about 3 hours to fully explore the state-space, finding no violations.

