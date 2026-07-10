import Lean

/-! Registers a stateful linter (async variant): `pre` counts each command, `post` reports the
running count. Registration happens at import time, satisfying `registerStatefulLinter`'s
initialization-only guard. -/

open Lean Elab Command

/-- State of the counting test linter. -/
structure Counter where
  count : Nat
  deriving TypeName

initialize
    registerStatefulLinter `StatefulLinterAsync.counter (Counter.mk 0)
      (pre := fun stx c _ =>
        pure <| if Parser.isTerminalCommand stx then c else { c with count := c.count + 1 })
      (post := fun stx c _ _ => do
        unless Parser.isTerminalCommand stx do
          logInfo m!"command count: {c.count}"
        pure c)
