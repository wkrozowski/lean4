import StatefulLinterAsync.Counter

/- Exercises the counting stateful linter in asynchronous mode (the default): `pre` counts each
command and `post` reports it, with the count threaded across commands via promises. -/

/-- info: command count: 1 -/
#guard_msgs in
def a := 1

/-- info: command count: 2 -/
#guard_msgs in
def b := 2

/-- info: command count: 3 -/
#guard_msgs in
def c := 3
