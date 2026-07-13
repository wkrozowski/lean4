import LinterTest.Readers

/- Exercises the emitter/readers group in *both* modes: `ra`/`rc` run async (the default), `rb` runs
sync via `set_option Elab.async false in`. Each command makes `emitter` count and the three readers
report the count read from `emitter`'s pre-phase handoff; the count threads across the mode switch. A
plain `/- -/` comment avoids a counted module-doc command. -/

/--
info: reader A sees count 1
---
info: reader B sees count 1
---
info: reader C sees count 1
-/
#guard_msgs (ordering := sorted) in
def ra := 1

set_option Elab.async false in
/--
info: reader A sees count 2
---
info: reader B sees count 2
---
info: reader C sees count 2
-/
#guard_msgs (ordering := sorted) in
def rb := 2

/--
info: reader A sees count 3
---
info: reader B sees count 3
---
info: reader C sees count 3
-/
#guard_msgs (ordering := sorted) in
def rc := 3
