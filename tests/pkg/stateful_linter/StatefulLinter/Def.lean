import Lean.Linter.StatefulLinter

open Lean Elab Command Linter StatefulLinter

initialize observedCountRef : IO.Ref Nat ← IO.mkRef 0

private def isCheck (stx : Syntax) : Bool := stx.isOfKind ``Lean.Parser.Command.check

initialize refA : StatefulLinterRef Nat ← registerStatefulLinter (σ := Nat) {
    name := `test.cmdCount
    init := 0
    run := fun stx n _ => do
      unless isCheck stx do return n
      observedCountRef.set (n + 1)
      return n + 1
  }

initialize refB : StatefulLinterRef Unit ← registerStatefulLinter (σ := Unit) {
    name := `test.readsPrevA
    init := ()
    run := fun stx _ ctx => do
      unless isCheck stx do return ()
      let prev := getPrev ctx refA
      let curr := getCurr ctx refA
      logInfo m!"prev was: {prev}, curr is: {curr}"
  }
