---- MODULE CLA_Generated_attempt_1_TTrace_1790012478 ----
EXTENDS Sequences, TLCExt, CLA_Generated_attempt_1, Toolbox, Naturals, TLC

_expression ==
    LET CLA_Generated_attempt_1_TEExpression == INSTANCE CLA_Generated_attempt_1_TEExpression
    IN CLA_Generated_attempt_1_TEExpression!expression
----

_trace ==
    LET CLA_Generated_attempt_1_TETrace == INSTANCE CLA_Generated_attempt_1_TETrace
    IN CLA_Generated_attempt_1_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        secondaryReleaseState = ()
        /\
        motorState = ()
        /\
        latchState = (<<"RTR", "RTC", "RTC">>)
    )
----

_init ==
    /\ motorState = _TETrace[1].motorState
    /\ secondaryReleaseState = _TETrace[1].secondaryReleaseState
    /\ latchState = _TETrace[1].latchState
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ motorState  = _TETrace[i].motorState
        /\ motorState' = _TETrace[j].motorState
        /\ secondaryReleaseState  = _TETrace[i].secondaryReleaseState
        /\ secondaryReleaseState' = _TETrace[j].secondaryReleaseState
        /\ latchState  = _TETrace[i].latchState
        /\ latchState' = _TETrace[j].latchState

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("CLA_Generated_attempt_1_TTrace_1790012478.json", _TETrace)

=============================================================================

 Note that you can extract this module `CLA_Generated_attempt_1_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `CLA_Generated_attempt_1_TEExpression.tla` file takes precedence 
  over the module `CLA_Generated_attempt_1_TEExpression` below).

---- MODULE CLA_Generated_attempt_1_TEExpression ----
EXTENDS Sequences, TLCExt, CLA_Generated_attempt_1, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `CLA_Generated_attempt_1` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        motorState |-> motorState
        ,secondaryReleaseState |-> secondaryReleaseState
        ,latchState |-> latchState
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_motorStateUnchanged |-> motorState = motorState'
        
        \* Format the `motorState` variable as Json value.
        \* ,_motorStateJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(motorState)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_motorStateModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].motorState # _TETrace[s-1].motorState
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE CLA_Generated_attempt_1_TETrace ----
\*EXTENDS IOUtils, CLA_Generated_attempt_1, TLC
\*
\*trace == IODeserialize("CLA_Generated_attempt_1_TTrace_1790012478.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE CLA_Generated_attempt_1_TETrace ----
EXTENDS CLA_Generated_attempt_1, TLC

trace == 
    <<
    ([secondaryReleaseState |-> <<"Inactive", "Inactive", "Inactive">>,motorState |-> <<"Operational", "Operational", "Operational">>,latchState |-> <<"RTC", "RTC", "RTC">>]),
    ([secondaryReleaseState |-> ,motorState |-> ,latchState |-> <<"RTR", "RTC", "RTC">>])
    >>
----


=============================================================================

---- CONFIG CLA_Generated_attempt_1_TTrace_1790012478 ----
CONSTANTS
    NumLatches = 3

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Mon Sep 21 19:41:18 CEST 2026