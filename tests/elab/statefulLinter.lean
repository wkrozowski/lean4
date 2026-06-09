import Lean

/-!
Tests the stateful-linter framework (`Lean.Linter.StatefulLinter`): a linter that folds a state
across commands, plus cross-linter reads of another linter's *previous*-command state
(`LinterStateCtx.getPrev`) and *current*-command state (`LinterStateCtx.getCurr`).

The three linters only act on `#check` commands so the output is a clean, deterministic trace.
`Elab.async` is disabled so the per-linter messages are merged in registration order. The linters are
registered imperatively via `run_cmd` (registration is idempotent by name, so this is safe).
-/

set_option linter.all false
set_option Elab.async false

open Lean Elab Command Linter

private def isCheck (stx : Syntax) : Bool := stx.isOfKind ``Lean.Parser.Command.check

run_cmd do
  -- Linter A: counts the `#check` commands it has seen (a self-fold over commands).
  let refA ← registerStatefulLinter (σ := Nat) {
    name := `test.cmdCount
    init := 0
    run := fun stx n _ => do
      unless isCheck stx do return n
      logInfo m!"A: count = {n + 1}"
      return n + 1
  }
  -- Linter B: reads linter A's *previous*-command count.
  let _ ← registerStatefulLinter (σ := Unit) {
    name := `test.readsPrevA
    init := ()
    run := fun stx _ ctx => do
      unless isCheck stx do return ()
      logInfo m!"B: A's previous count = {ctx.getPrev refA}"
  }
  -- Linter C: reads linter A's *current*-command count (acyclic: registered after A).
  let _ ← registerStatefulLinter (σ := Unit) {
    name := `test.readsCurrA
    init := ()
    run := fun stx _ ctx => do
      unless isCheck stx do return ()
      logInfo m!"C: A's current count = {ctx.getCurr refA}"
  }

#check 1
#check 2
#check 3
