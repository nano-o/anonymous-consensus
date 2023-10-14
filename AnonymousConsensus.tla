--------------- MODULE AnonymousConsensus -------------------

\* Binary, obstruction-free consensus using anonymous registers

EXTENDS Naturals, FiniteSets

CONSTANTS
    P \* the processes
,   Bot \* default value

N == Cardinality(P)
Rs == 1..2*N-1 \* The registers

(*--algorithm Algo
  { variables
        r = [i \in Rs |-> Bot]; \* the anonymous registers and their contents
    define {
    }
    process (proc \in P)
        variables
            pref \in {0,1}; \* preference
            read = {};
            count = [v \in {0,1} |-> 0];
            decision = Bot;
    {
l0: while (TRUE) {
l1:     while (\neg (read = Rs \/ count[0] > N \/ count[1] > N)) {
            with (i \in Rs \ read) {
                read := read \cup {i};
                with (v = r[i])
                if (v # Bot)
                    count[v] := count[v]+1;
            }
        };
l2:     if (count[0] = 2*N-1 \/ count[1] = 2*N-1)
            with (v \in {0,1}) {
                when count[v] = 2*N-1;
                decision := v };
        if (count[0] >= N \/ count[1] >= N)
            with (v \in {0,1}) {
                when count[v] >= N;
                pref := v  };
        with (i \in Rs)
            r[i] := pref;
        count := [v \in {0,1} |-> 0];
        read := {}}
    }
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "342ac330" /\ chksum(tla) = "c69677b3")
VARIABLES r, pc, pref, read, count, decision

vars == << r, pc, pref, read, count, decision >>

ProcSet == (P)

Init == (* Global variables *)
        /\ r = [i \in Rs |-> Bot]
        (* Process proc *)
        /\ pref \in [P -> {0,1}]
        /\ read = [self \in P |-> {}]
        /\ count = [self \in P |-> [v \in {0,1} |-> 0]]
        /\ decision = [self \in P |-> Bot]
        /\ pc = [self \in ProcSet |-> "l0"]

l0(self) == /\ pc[self] = "l0"
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ UNCHANGED << r, pref, read, count, decision >>

l1(self) == /\ pc[self] = "l1"
            /\ IF \neg (read[self] = Rs \/ count[self][0] > N \/ count[self][1] > N)
                  THEN /\ \E i \in Rs \ read[self]:
                            /\ read' = [read EXCEPT ![self] = read[self] \cup {i}]
                            /\ LET v == r[i] IN
                                 IF v # Bot
                                    THEN /\ count' = [count EXCEPT ![self][v] = count[self][v]+1]
                                    ELSE /\ TRUE
                                         /\ count' = count
                       /\ pc' = [pc EXCEPT ![self] = "l1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l2"]
                       /\ UNCHANGED << read, count >>
            /\ UNCHANGED << r, pref, decision >>

l2(self) == /\ pc[self] = "l2"
            /\ IF count[self][0] = 2*N-1 \/ count[self][1] = 2*N-1
                  THEN /\ \E v \in {0,1}:
                            /\ count[self][v] = 2*N-1
                            /\ decision' = [decision EXCEPT ![self] = v]
                  ELSE /\ TRUE
                       /\ UNCHANGED decision
            /\ IF count[self][0] >= N \/ count[self][1] >= N
                  THEN /\ \E v \in {0,1}:
                            /\ count[self][v] >= N
                            /\ pref' = [pref EXCEPT ![self] = v]
                  ELSE /\ TRUE
                       /\ pref' = pref
            /\ \E i \in Rs:
                 r' = [r EXCEPT ![i] = pref'[self]]
            /\ count' = [count EXCEPT ![self] = [v \in {0,1} |-> 0]]
            /\ read' = [read EXCEPT ![self] = {}]
            /\ pc' = [pc EXCEPT ![self] = "l0"]

proc(self) == l0(self) \/ l1(self) \/ l2(self)

Next == (\E self \in P: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

Safety == \A p1,p2 \in P : decision[p1] # Bot /\ decision[p2] # Bot =>
    decision[p1] = decision[p2]

Canary1 == \A p \in P : decision[p] = Bot
Canary2 == \E p \in P : decision[p] = Bot

=============================================================
