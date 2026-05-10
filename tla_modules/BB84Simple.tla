----------------------------- MODULE BB84Simple -----------------------------
EXTENDS Naturals

QStates == {"|0>","|1>","|+>","|->"}
ZStates == {"|0>","|1>"}
XStates == {"|+>","|->"}
Bases == {"Z","X"}
Bits  == {0,1}
Basis(s) == IF s \in ZStates THEN "Z" ELSE "X"
BitValue(s) == IF s \in {"|0>","|+>"} THEN 0 ELSE 1
StatesOfBasis(b) == IF b = "Z" THEN ZStates ELSE XStates

VARIABLES aliceState, channelState, bobBasis, bobResult

vars == <<aliceState, channelState, bobBasis, bobResult>>

Init == /\ aliceState \in QStates
        /\ channelState = aliceState
        /\ bobBasis \in Bases
        /\ bobResult \in Bits

Transmit == /\ \E b \in Bases : channelState' \in StatesOfBasis(b)
            /\ UNCHANGED <<aliceState, bobBasis, bobResult>>
    
Measure ==/\ IF Basis(channelState) = bobBasis
             THEN bobResult' = BitValue(channelState)
             ELSE bobResult' \in Bits
          /\ UNCHANGED <<aliceState, channelState, bobBasis>>

Next == Transmit \/ Measure

Spec == Init /\ [][Next]_vars


Sifted == Basis(aliceState) = bobBasis
AliceKeyBit == IF Sifted THEN BitValue(aliceState) ELSE "discard"
BobKeyBit == IF Sifted THEN bobResult ELSE "discard"

KeyAgreement == Sifted => AliceKeyBit = BobKeyBit

Disturbance == Sifted /\ bobResult # BitValue(aliceState)

ChannelIntegrity == channelState = aliceState

IdealCorrectness == Basis(aliceState) = bobBasis 
                    => bobResult = BitValue(aliceState)

PerfectChannelCorrectness == ChannelIntegrity => IdealCorrectness

KeyTypeSafety == AliceKeyBit \in Bits \cup {"discard"} /\ BobKeyBit \in Bits \cup {"discard"}

=============================================================================
\* Modification History
\* Last modified Thu Mar 12 01:45:38 CET 2026 by tianxiang.lu
\* Created Thu Mar 12 00:36:55 CET 2026 by tianxiang.lu
