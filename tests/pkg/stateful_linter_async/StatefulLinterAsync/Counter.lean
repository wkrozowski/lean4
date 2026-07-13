import Lean

/-! Registers a group of stateful linters (async variant). `emitter` counts commands: its `pre`
produces a `Payload` handoff (declining on terminal commands such as end-of-input), its `post` folds
that into a persistent `Counter`. `readerA`/`readerB`/`readerC` have no `pre` pass (the default) and no
state others read (their handles are discarded); their `post` reads `emitter`'s pre-phase `Payload`
through `emitter`'s handle — exercising several post phases consuming one pre phase, handle-based
cross-linter reads, `τ ≠ σ`, declining, and the default `pre`. Registration happens at import time,
satisfying `registerStatefulLinter`'s initialization-only guard. -/

open Lean Elab Command

/-- Persistent (`σ`) state of `emitter`: the running command count. -/
structure Counter where
  count : Nat

/-- Pre-phase handoff (`τ`) of `emitter`: the count computed for the current command. -/
structure Payload where
  current : Nat

/-- Registers a post-only linter that reports the count `emitter` staged this command. It reads
`emitter` through its handle; its own handoff type is irrelevant, so we fix `τ := Unit` and discard
the handle it returns (nobody reads this linter). -/
def registerReader (emitter : StatefulLinter Counter Payload) (name : Name) (label : String) :
    IO Unit := do
  let _ ← registerStatefulLinter (τ := Unit) name (Counter.mk 0)
    (post := fun _ self _ _ readPre => do
      if let some p := readPre emitter then
        logInfo m!"{label} sees count {p.current}"
      pure self)

initialize emitter : StatefulLinter Counter Payload ←
  registerStatefulLinter `StatefulLinterAsync.emitter (Counter.mk 0)
    (pre := fun stx self _ =>
      -- decline on terminal commands (e.g. end-of-input)
      pure <| if Parser.isTerminalCommand stx then none else some { current := self.count + 1 })
    (post := fun _ self preState _ _ =>
      -- fold the handoff into the persistent counter, keeping the old count when `pre` declined
      pure { count := (preState.map Payload.current).getD self.count })

initialize
  registerReader emitter `StatefulLinterAsync.readerA "reader A"
  registerReader emitter `StatefulLinterAsync.readerB "reader B"
  registerReader emitter `StatefulLinterAsync.readerC "reader C"
