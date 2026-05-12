import Lean
open Lean Elab Command

/-!
Regression test for `Ipc.waitForMessage` on a `$/lean/fileProgress fatalError`
notification: the runner must abort instead of blocking on a diagnostic that
can never be emitted by a dead worker.

The `crash_now` command terminates the file worker via `IO.Process.forceExit`,
so the `waitFor` directive on the line after it cannot succeed normally. The
watchdog reacts by sending `fileProgress` with `kind = fatalError`, which
`waitForMessage` picks up and turns into a Lean-level exception. The test
framework checks `TEST_EXIT=1` and the resulting error message via
`.out.expected`.

Avoid mentioning the literal directive syntax in this docstring -- the runner
parses every line containing `--` looking for a directive.
-/

elab "crash_now" : command => IO.Process.forceExit 9

crash_now
   --^ waitFor: nope
