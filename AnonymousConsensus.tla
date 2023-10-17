--------------- MODULE AnonymousConsensus -------------------

\* Obstruction-free set-agreement using anonymous registers and anonymous processes

EXTENDS Naturals, FiniteSets

CONSTANTS
    P \* the anonymous processes
,   V \* consensus values
,   Bot \* default value
,   Rs \* the anonymous registers

N == Cardinality(P)
NR == Cardinality(Rs)

(*--algorithm Algo
  { variables
        regs = [r \in Rs |-> Bot]; \* the anonymous registers and their contents
    process (proc \in P)
        variables
            pref \in V; \* preference
            read = {};
            count = [v \in V |-> 0];
            decision = Bot;
    {
l0: while (TRUE) {
l1:     while (read # Rs) {
            with (r \in Rs \ read) {
                read := read \cup {r};
                with (v = regs[r])
                if (v # Bot)
                    count[v] := count[v]+1;
            }
        };
l2:     if (\E v \in V : count[v] = NR)
            with (v \in V) {
                when count[v] = NR;
                decision := v };
        if (\E v \in V : 2*count[v] > NR)
            with (v \in V) {
                when 2*count[v] > NR;
                pref := v  };
        with (r \in Rs)
            regs[r] := pref;
        count := [v \in V |-> 0];
        read := {};
        if (decision # Bot)
            goto "Done";
    }}
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "e84b9d43" /\ chksum(tla) = "36e54315")
VARIABLES regs, pc, pref, read, count, decision

vars == << regs, pc, pref, read, count, decision >>

ProcSet == (P)

Init == (* Global variables *)
        /\ regs = [r \in Rs |-> Bot]
        (* Process proc *)
        /\ pref \in [P -> V]
        /\ read = [self \in P |-> {}]
        /\ count = [self \in P |-> [v \in V |-> 0]]
        /\ decision = [self \in P |-> Bot]
        /\ pc = [self \in ProcSet |-> "l0"]

l0(self) == /\ pc[self] = "l0"
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << regs, pref, read, count, decision >>

l1(self) == /\ pc[self] = "l1"
            /\ IF read[self] # Rs
                  THEN /\ \E r \in Rs \ read[self]:
                            /\ read' = [read EXCEPT ![self] = read[self] \cup {r}]
                            /\ LET v == regs[r] IN
                                 IF v # Bot
                                    THEN /\ count' = [count EXCEPT ![self][v] = count[self][v]+1]
                                    ELSE /\ TRUE
                                         /\ count' = count
                       /\ pc' = [pc EXCEPT ![self] = "l1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l2"]
                       /\ UNCHANGED << read, count >>
            /\ UNCHANGED << regs, pref, decision >>

l2(self) == /\ pc[self] = "l2"
            /\ IF \E v \in V : count[self][v] = NR
                  THEN /\ \E v \in V:
                            /\ count[self][v] = NR
                            /\ decision' = [decision EXCEPT ![self] = v]
                  ELSE /\ TRUE
                       /\ UNCHANGED decision
            /\ IF \E v \in V : 2*count[self][v] > NR
                  THEN /\ \E v \in V:
                            /\ 2*count[self][v] > NR
                            /\ pref' = [pref EXCEPT ![self] = v]
                  ELSE /\ TRUE
                       /\ pref' = pref
            /\ \E r \in Rs:
                 regs' = [regs EXCEPT ![r] = pref'[self]]
            /\ count' = [count EXCEPT ![self] = [v \in V |-> 0]]
            /\ read' = [read EXCEPT ![self] = {}]
            /\ IF decision'[self] # Bot
                  THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l0"]

proc(self) == l0(self) \/ l1(self) \/ l2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in P: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Consensus == \A p1,p2 \in P : decision[p1] # Bot /\ decision[p2] # Bot =>
    decision[p1] = decision[p2]

SetConsensus == \* we must decide at most N-1 values
    LET Decided == {v \in V : \E p \in P : decision[p] = v}
    IN  Cardinality(Decided) < N

Canary0 == \A p \in P : pc[p] # "l2"
Canary1 == \A p \in P : decision[p] = Bot
Canary2 == \E p \in P : decision[p] = Bot

=============================================================
