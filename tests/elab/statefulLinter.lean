import Lean

set_option Elab.async false

open Lean Elab Command Linter StatefulLinter

private def isCheck (stx : Syntax) : Bool := stx.isOfKind ``Lean.Parser.Command.check

initialize refA : Linter.StatefulLinter.StatefulLinterRef Nat ← Linter.StatefulLinter.registerStatefulLinter (σ := Nat) {
    name := `test.cmdCount
    init := 0
    run := fun stx n _ => do
      unless isCheck stx do return n
      logInfo m!"A: count = {n + 1}"
      return n + 1
  }

initialize refB : StatefulLinterRef Unit ← registerStatefulLinter (σ := Unit) {
    name := `test.readsPrevA
    init := ()
    run := fun stx _ ctx => do
      unless isCheck stx do return ()
      logInfo m!"B: A's previous count = {getPrev ctx refA}"
  }

initialize _ : StatefulLinterRef Unit ← registerStatefulLinter (σ := Unit) {
    name := `test.readsCurrA
    init := ()
    run := fun stx _ ctx => do
      unless isCheck stx do return ()
      logInfo m!"C: A's current count = {getCurr ctx refA}"
  }

#check 1
#check 2
#check 3
