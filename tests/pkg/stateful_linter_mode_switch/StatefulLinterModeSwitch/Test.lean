import StatefulLinterModeSwitch.Counter

/- Threads the command count across `Elab.async` mode switches. `a`/`c` run async (the default); `b`/`d`
run sync via `set_option Elab.async false in` wrapping the `#guard_msgs in def` (so the option is in
scope when the linter runs on the inner `def`, and the outer command is skipped as it contains
`#guard_msgs`). The count must stay sequential across every transition. A plain `/- -/` comment (not a
`/-! -/` module docstring) is used so no extra module-doc command is counted. -/

/-- info: count: 1 -/
#guard_msgs in
def a := 1

set_option Elab.async false in
/-- info: count: 2 -/
#guard_msgs in
def b := 2

/-- info: count: 3 -/
#guard_msgs in
def c := 3

set_option Elab.async false in
/-- info: count: 4 -/
#guard_msgs in
def d := 4
