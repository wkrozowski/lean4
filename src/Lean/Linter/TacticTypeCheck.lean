/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
import Lean.Elab.Command
import Lean.Linter.Util
import Lean.Meta.Check
import Lean.Meta.Diagnostics

namespace Lean.Linter

open Lean Elab Command
open Lean.Linter (logLint)

/--
Warn when the goal target is not type-correct at `.instances` transparency.
This can happen when e.g. `unfold` leaves hypotheses whose types still refer to
the pre-unfolded definition, preventing `rw`/`simp` from matching patterns.
-/
register_builtin_option linter.tacticCheckInstances : Bool := {
  defValue := false
  descr := "enable the linter that type-checks every tactic goal at `.instances` transparency"
}

/-- A linter that runs `Meta.check _ .instances` on every tactic goal. -/
def tacticCheckInstances : Linter where
  run _ _cmdStx := do
    -- Do *not* check `linter.all` here, this linter is purely for debugging
    unless (← linter.tacticCheckInstances.getM) do
      return
    let infoTrees := (← get).infoState.trees.toArray
    -- Once any tactic step in this command has produced a warning, suppress
    -- all further checks: a bad lctx typically persists across many tactic
    -- steps
    let warned : IO.Ref Bool ← IO.mkRef false
    for tree in infoTrees do
      -- `postNode` so children are visited before parents: leaf tactic infos
      -- (the actual user-written `unfold`, `rw`, ...) fire before the
      -- enclosing tactic-sequence node, which has the syntax of the whole
      -- `by` block and would otherwise be the warning location.
      tree.visitM' (postNode := fun ci info _ => do
        if (← warned.get) then return
        let .ofTacticInfo ti := info | return
        -- Check `goalsBefore` then `goalsAfter`.
        -- - `goalsBefore` catches an initially-bad goal at the first tactic.
        -- - `goalsAfter` catches the result of this tactic — so `unfold foo`
        --   gets blamed, not the next tactic whose `goalsBefore` inherits it.
        --
        -- For each goal, we run `check` first at `.default` transparency
        -- (bailing out if it fails — that's a more fundamental problem), then
        -- (after resetting the unfold counter) at `.instances`. If the
        -- `.instances` check fails, the defs unfolded at `.default` but not at
        -- `.instances` are the candidates for `@[implicit_reducible]` and get
        -- reported to the user. The pattern mirrors `mkUnfoldAxiomsNote` in
        -- `Lean.Meta.Check`.
        -- `kind` selects the wording of the warning:
        --   * "initial" — the failure is in `goalsBefore` of the first tactic
        --     (i.e. the `by` block started with a bad goal).
        --   * "produced" — the failure is in `goalsAfter` of this tactic
        --     (i.e. this tactic left the goal in a bad state).
        let checkGoal (kind : String) (g : MVarId) : MetaM (Option MessageData) := do
          let some mdecl := (← getMCtx).findDecl? g | return none
          let target ← instantiateMVars mdecl.type
          let origDiag := (← get).diag
          let result : Option MessageData ← Meta.withLCtx mdecl.lctx #[] <|
              withOptions (diagnostics.set · true) do
            -- If the goal is not even type-correct at `.default`, bail out —
            -- this is a different (more fundamental) problem.
            try Meta.check target .default catch _ => return none
            let counterDefault := (← get).diag.unfoldCounter
            -- Reset and try at `.instances`.
            modify ({ · with diag := origDiag })
            try
              Meta.check target .instances
              return none
            catch _ =>
              let counterInst := (← get).diag.unfoldCounter
              let diff := Meta.subCounters counterDefault counterInst
              let env ← getEnv
              let candidates : List MessageData :=
                diff.toList.filterMap fun (n, count) => do
                  guard <| count > 0
                  guard <| getReducibilityStatusCore env n matches .semireducible
                  guard <| !Meta.isInstanceCore env n
                  return m!"{.ofConstName n}"
              if candidates.isEmpty then
                return none
              let remedy : MessageData := match kind with
                | "initial" => "consider rephrasing the goal or marking"
                | _         => "consider using propositional rewriting or marking"
              return some m!"{kind} tactic goal is not type-correct at \
                `.instances` transparency; {remedy} some of the following as \
                `@[implicit_reducible]`:\
                {indentD (.joinSep candidates Format.line)}"
          -- Always restore the original diagnostics snapshot.
          modify ({ · with diag := origDiag })
          return result
        let check (kind : String) (goals : List MVarId) : MetaM (Option MessageData) := do
          for g in goals do
            if let some msg ← checkGoal kind g then
              return some msg
          return none
        let ctxBefore : ContextInfo := { ci with mctx := ti.mctxBefore }
        let ctxAfter  : ContextInfo := { ci with mctx := ti.mctxAfter }
        let failure : Option MessageData ← liftM do
          let m₁ ← ctxBefore.runMetaM {} (check "initial" ti.goalsBefore)
          if m₁.isSome then return m₁
          ctxAfter.runMetaM {} (check "produced" ti.goalsAfter)
        if let some msg := failure then
          warned.set true
          logLint linter.tacticCheckInstances ti.stx msg)

builtin_initialize addLinter tacticCheckInstances
