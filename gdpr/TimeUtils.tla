---------------------------- MODULE TimeUtils ----------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANTS
    MonthRange,
    DayRange,
    HourRange,
    MinuteRange, 
    YearRange,
    FixedEndTime
\* TLC-compatible Min/Max for finite sets of numbers, avoiding CHOOSE
Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : x >= y



MinutesInDay == 24 * 60
FixedEpochYear == 2020

IsLeapYear(year) ==
    LET
        div4    == year % 4 = 0
        notDiv100 == year % 100 /= 0
        div400  == year % 400 = 0
    IN
        div4 /\ (notDiv100 \/ div400)

DaysInMonth ==
    [i \in 1..12 |->
        CASE i = 1 -> 31
        [] i = 2 -> 28
        [] i = 3 -> 31
        [] i = 4 -> 30
        [] i = 5 -> 31
        [] i = 6 -> 30
        [] i = 7 -> 31
        [] i = 8 -> 31
        [] i = 9 -> 30
        [] i = 10 -> 31
        [] i = 11 -> 30
        [] i = 12 -> 31
    ]

RECURSIVE DaysUpToMonth(_)

DaysUpToMonth(tp) ==
    IF tp.month = 1
    THEN 0
    ELSE DaysUpToMonth([tp EXCEPT !.month = tp.month - 1])
         + IF tp.month = 2 /\ IsLeapYear(tp.year)
           THEN 29
           ELSE DaysInMonth[tp.month - 1]




LeapDaysSinceEpoch(y) ==
    LET d == y - FixedEpochYear
    IN  (d \div 4) - (d \div 100) + (d \div 400)

LinearTime(tp) ==
    LET
        yearOffset == (tp.year - FixedEpochYear) * 365 * MinutesInDay
        leapYearOffset == LeapDaysSinceEpoch(tp.year) * MinutesInDay
        monthOffset == DaysUpToMonth(tp) * MinutesInDay
        dayOffset == (tp.day - 1) * MinutesInDay
        hourOffset == tp.hour * 60
        minuteOffset == tp.minute
    IN
        yearOffset + leapYearOffset + monthOffset + dayOffset + hourOffset + minuteOffset

\* Predicates for time comparison and duration.
Before(t1, t2) == LinearTime(t1) < LinearTime(t2)
After(t1, t2) == LinearTime(t1) > LinearTime(t2)
TimeBetween(t_start, t_end, t_test) == /\ Before(t_start, t_test) /\ Before(t_test, t_end)

\* Help function for calculation if a time point occur within 72 hours.
Within72Hours(start_time, end_time) == (LinearTime(end_time) - LinearTime(start_time)) <= 72 * 60

\* Helper: Extract all time points from a set of events
\* EventTimePoints(events) == {tp \in TimePoints : \E e \in events : e.time = tp \/ e.end_time = tp}

\*  TimePoints == {e.time : e \in InitialEvents} \cup {e.end_time : e \in InitialEvents}
TimePoints(events) == {e.time : e \in events} \cup {e.end_time : e \in events}

\*
\*TimePoints == { [year |-> y, month |-> m, day |-> d, hour |-> h, minute |-> min] :
\*                  y \in YearRange,
\*                  m \in MonthRange,
 \*                 d \in DayRange,
 \*                 h \in HourRange,
 \*                 min \in MinuteRange }
\* The earliest time point within a set of events
MinTime(events) ==
  IF events = {} THEN
    [year |-> FixedEpochYear, month |-> 12, day |-> 31, hour |-> 23, minute |-> 59] \* default far-future time
  ELSE
    \* Avoid CHOOSE: use the minimum by enumeration
      LET times == TimePoints(events)
    IN  
      LET minVal == Min({LinearTime(t) : t \in times}) IN
        CHOOSE t \in times : LinearTime(t) = minVal
    \* Pick the minimum by folding over the set
      \* If there are multiple minima, pick the first in the set
      \* This is TLC-friendly and avoids CHOOSE
      \* Use the following definition:
      \* Fold over the set to find the minimum
      \* (TLC does not have a built-in fold, so use a workaround)
      \* Use the minimum function on the set
      \* This works because LinearTime returns a number
      \* Find the set of times with the minimum LinearTime value

\* The latest time point within a set of events
MaxTime(events) ==
  IF events = {} THEN
    [year |->  Max({FixedEndTime, FixedEpochYear} \cup YearRange), month |-> 12, day |-> 31, hour |-> 23, minute |-> 59] \* default far-future time
  ELSE
      LET times == TimePoints(events)
    IN
      LET maxVal == Max({LinearTime(t) : t \in times}) IN
        CHOOSE t \in times : LinearTime(t) = maxVal

=============================================================================

