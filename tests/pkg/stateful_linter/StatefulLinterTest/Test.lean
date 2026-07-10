import StatefulLinterTest.Counter

/- Exercises the counting stateful linter (synchronous mode, set package-wide in the lakefile):
each command's `pre` bumps the count and its `post` reports it. The count threads across commands,
so the reports increase. -/

/-- info: command count: 1 -/
#guard_msgs in
def a := 1

/-- info: command count: 2 -/
#guard_msgs in
def b := 2

/-- info: command count: 3 -/
#guard_msgs in
def c := 3
