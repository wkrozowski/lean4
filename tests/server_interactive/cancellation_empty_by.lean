import Lean.Server.Test.Cancel
import Lean.Elab.Tactic.Try
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
open Lean.Server.Test.Cancel

/-!
Test cancellation propagation through `elabEmptyByAsTry`. With
`tactic.tryOnEmptyBy true` an empty `by` (the proof `:= by` with nothing
following) spawns a `wrapAsyncAsSnapshot` task that runs `try?`. The
outer snapshot's cancel token (`T_outer`) is registered with
`Core.logSnapshotTask`; on re-elaboration `cancelRec` walks the
snapshot tree and sets it.

The `[try_suggestion]` generator runs in MetaM inside the empty-`by`
snapshot task, so `(← read).cancelTk?` is `T_outer`. It registers a
test task under label `"T_outer"` (via `mkTestTask`) on the first
invocation and arranges `T_outer.onSet` to resolve it; the returned
candidate `wait_for_test_task "T_outer"` blocks until the task fires.

`t1`'s `wait_for_cancel_once_async` is used purely to publish the
`"blocked"` diagnostic the runner waits for. On re-elaboration
`cancelRec` walks both `t1`'s tree and the empty-`by` example's
tree; firing `T_outer` resolves the shared task and the snapshot
task body completes. The second elaboration's invocation observes
the already-resolved task and returns immediately.

If `elabEmptyByAsTry` passes `cancelTk? := none` to
`Core.logSnapshotTask`, `cancelRec` cannot reach `T_outer`. The
snapshot task body's wait blocks until `T_outer` is dropped; since
the body holds `T_outer` alive (via `wrapAsync`'s ctx) until it
returns, `T_outer` does not drop, the wait does not return, and the
runner times out. If `elabEmptyByAsTry` additionally fails to plumb
`cancelTk` into `wrapAsyncAsSnapshot`, no `onSet` resolver is
registered, the promise drops, and `wait_for_test_task` surfaces
the explicit "task dropped" diagnostic on stderr.
-/

namespace TestEmptyBy

opaque UnsolvableProp : Prop

@[try_suggestion]
def tracerSuggestion (_goal : MVarId) (_info : Try.Info) :
    MetaM (Array (TSyntax `tactic)) := do
  -- Register the test task on the first call only; later calls reuse the
  -- existing entry and so observe the same (eventually resolved) task.
  if let some prom ← mkTestTask "T_outer" then
    if let some cancelTk := (← readThe Core.Context).cancelTk? then
      cancelTk.onSet (do prom.resolve ())
  return #[← `(tactic| wait_for_test_task "T_outer")]

end TestEmptyBy

set_option tactic.tryOnEmptyBy true

example : True := by
  trivial
       --^ waitFor: blocked
       --^ insert: "; skip"
       --^ sync

theorem t1 : True := by
  wait_for_cancel_once_async
  trivial

example : TestEmptyBy.UnsolvableProp := by


