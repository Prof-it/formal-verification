----------------------------- MODULE BB84QKD -----------------------------
EXTENDS Naturals, Sequences

CONSTANT N

(*
Symbolic BB84 quantum states using Dirac notation
*)

QStates == {"|0⟩","|1⟩","|+⟩","|−⟩"}
ZStates == {"|0⟩","|1⟩"}
XStates == {"|+⟩","|−⟩"}

Bases == {"Z","X"}
Bits  == {0,1}

Basis(s) ==
    IF s \in ZStates THEN "Z" ELSE "X"

BitValue(s) ==
    IF s \in {"|0⟩","|+⟩"} THEN 0 ELSE 1

StatesOfBasis(b) ==
    IF b = "Z" THEN ZStates ELSE XStates


MeasurementOutcome(s, b) ==
    IF Basis(s) = b
        THEN {s}
        ELSE StatesOfBasis(b)

VARIABLES
    aliceStates,
    channelStates,
    bobBases,
    bobResults,
    round,
    phase

vars ==
    <<aliceStates, channelStates, bobBases, bobResults, round, phase>>


Init ==
    /\ aliceStates \in [1..N -> QStates]
    /\ channelStates = aliceStates
    /\ bobBases \in [1..N -> Bases]
    /\ bobResults \in [1..N -> Bits]
    /\ round = 1
    /\ phase = "transmit"


(*
Transmit models intercept-resend disturbance
*)

Transmit ==
    /\ phase = "transmit"
    /\ round <= N
    /\ \E b \in Bases :
        \E s \in MeasurementOutcome(channelStates[round], b) :
            channelStates' =
                [channelStates EXCEPT ![round] = s]
    /\ phase' = "measure"
    /\ UNCHANGED <<aliceStates, bobBases, bobResults, round>>


Measure ==
    /\ phase = "measure"
    /\ round <= N
    /\ IF Basis(channelStates[round]) = bobBases[round]
          THEN
              bobResults' =
                  [bobResults EXCEPT
                      ![round] = BitValue(channelStates[round])]
          ELSE
              \E r \in Bits :
                  bobResults' =
                      [bobResults EXCEPT ![round] = r]
    /\ round' = round + 1
    /\ phase' = "transmit"
    /\ UNCHANGED <<aliceStates, channelStates, bobBases>>


Next ==
    Transmit \/ Measure


Spec ==
    Init /\ [][Next]_vars


(*
Ideal BB84 correctness property
*)

Finished == round > N

IdealCorrectness(i) ==
    /\ i \in 1..N
    /\ Basis(aliceStates[i]) = bobBases[i]
    => bobResults[i] = BitValue(aliceStates[i])


AllIdealCorrect ==
    Finished =>
        \A i \in 1..N : IdealCorrectness(i)


(*
BB84 sifting phase
*)

MatchingRounds ==
    { i \in 1..N : Basis(aliceStates[i]) = bobBases[i] }


AliceKey ==
    [ i \in MatchingRounds |-> BitValue(aliceStates[i]) ]


BobKey ==
    [ i \in MatchingRounds |-> bobResults[i] ]


    
KeyAgreement ==
    Finished => AliceKey = BobKey


(*
Error detection property
*)

Disturbance(i) ==
    /\ i \in 1..N
    /\ Basis(aliceStates[i]) = bobBases[i]
    /\ bobResults[i] # BitValue(aliceStates[i])


SomeDisturbance ==
    \E i \in 1..N : Disturbance(i)

=============================================================================