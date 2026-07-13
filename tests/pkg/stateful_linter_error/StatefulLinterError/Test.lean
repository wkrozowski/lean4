import StatefulLinterError.Counter

/- Error handling on both stateful-linter paths: `a` runs async (default), `b` runs sync (via
`set_option Elab.async false in` wrapping the `#guard_msgs in def`). Each command logs both throwers'
errors *and* the working `counter`'s count, showing that a failing linter is logged, isolated from the
others, and non-fatal to threading (the count keeps advancing). A plain `/- -/` comment avoids a
counted module-doc command. -/

/--
error: stateful linter StatefulLinterError.preThrower (pre) failed: pre boom
---
info: count: 1
---
error: stateful linter StatefulLinterError.postThrower (post) failed: post boom
-/
#guard_msgs in
def a := 1

set_option Elab.async false in
/--
error: stateful linter StatefulLinterError.preThrower (pre) failed: pre boom
---
info: count: 2
---
error: stateful linter StatefulLinterError.postThrower (post) failed: post boom
-/
#guard_msgs in
def b := 2
