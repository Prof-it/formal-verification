---------------------------- MODULE TimeUtils ----------------------------
EXTENDS Naturals, Sequences, TLC


\* Use a fixed epoch for a consistent time base.
FixedEpochYear == 2000
YearRange == FixedEpochYear .. FixedEpochYear + 50



MinutesInDay == 24 * 60


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

Within72Hours(start_time, end_time) == (LinearTime(end_time) - LinearTime(start_time)) <= 72 * 60


MinTime(events) ==
  LET times == {e.time : e \in events}
  IN
    CHOOSE t \in times: \A t_other \in times: LinearTime(t) <= LinearTime(t_other)

MaxTime(events) ==
  LET times == {e.time : e \in events}
  IN
    CHOOSE t \in times: \A t_other \in times: LinearTime(t) >= LinearTime(t_other)

=============================================================================