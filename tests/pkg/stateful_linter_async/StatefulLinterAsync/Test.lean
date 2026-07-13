import StatefulLinterAsync.Counter

/- Exercises the linter group in asynchronous mode (the default): each command makes `emitter` count,
and the three readers each report the count they read out of `emitter`'s pre-phase handoff, with the
count threaded across commands via promises.

A plain `/- -/` comment (not a `/-! -/` module docstring) is used deliberately: a module docstring is
itself a command, which the now-active linters would count and report before the first `def`. -/

/--
info: reader A sees count 1
---
info: reader B sees count 1
---
info: reader C sees count 1
-/
#guard_msgs (ordering := sorted) in
def a := 1

/--
info: reader A sees count 2
---
info: reader B sees count 2
---
info: reader C sees count 2
-/
#guard_msgs (ordering := sorted) in
def b := 2

/--
info: reader A sees count 3
---
info: reader B sees count 3
---
info: reader C sees count 3
-/
#guard_msgs (ordering := sorted) in
def c := 3
