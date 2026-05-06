/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module
public import Lean.Elab.Command
public import Lean.Parser.Term
public section
open Lean Elab Linter Command

namespace Lean.Linter.Extra

/--
The `multiGoal` linter warns when a tactic finishes with goals in scope that
were already in scope before it ran. The intent is to push users to focus on
a single goal at a time using `·`, `case`, `focus`, or `on_goal`.

Tactics whose purpose is to operate on multiple goals (combinators, sequence
wrappers, `<;>`, `try`, `repeat`, `·`, `case`, `all_goals`, ...) are recognised
*structurally* — by the fact that the real work happens in a descendant
`TacticInfo` — rather than by name. Pure reorderings and no-ops are recognised
*behaviourally* by comparing the multiset of goals before and after. The small
`registerMultiGoalSafe` registry covers anything that escapes both rules.
-/
public register_option linter.extra.multiGoal : Bool := {
  defValue := false
  descr := "enable the multiGoal linter"
}

/--
Persistent registry of `SyntaxNodeKind`s that are exempt from the `multiGoal`
linter despite not being recognisable structurally or behaviourally. Use
sparingly — most exemptions should fall out of the analysis itself.
-/
builtin_initialize multiGoalSafeExt :
    SimplePersistentEnvExtension SyntaxNodeKind (Std.HashSet SyntaxNodeKind) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun arrs => arrs.foldl (init := {}) fun acc arr =>
      arr.foldl (init := acc) (·.insert ·)
    addEntryFn  := fun s k => s.insert k
    toArrayFn   := fun es => es.toArray
  }

/-- Mark `kind` as exempt from the `multiGoal` linter. -/
public def registerMultiGoalSafe (kind : SyntaxNodeKind) : CoreM Unit :=
  modifyEnv fun env => multiGoalSafeExt.addEntry env kind

/--
Returns `true` if `kind` is a member of the `tactic` parser category. This
filters out parser tokens, tactic-sequence wrappers (`tacticSeq`,
`tacticSeq1Indented`, `tacticSeqBracketed`), `null`, separators, and other
syntax kinds that appear as `TacticInfo` records but do not represent
user-level tactic applications.
-/
def isTacticKind (env : Environment) (kind : SyntaxNodeKind) : Bool :=
  match (Parser.parserExtension.getState env).categories.find? `tactic with
  | some cat => cat.kinds.contains kind
  | none     => false

/--
Returns `true` if `t` carries a `TacticInfo` at the root or anywhere below.
A `TacticInfo` node whose children also contain `TacticInfo`s is structural
(a combinator, sequence, `try`, `repeat`, `<;>`, `·`, `case`, `focus`, ...)
and is skipped: the linter inspects only the leaf invocations underneath.
-/
partial def hasTacticInfo : InfoTree → Bool
  | .node (.ofTacticInfo _) _ => true
  | .node _ args              => args.any hasTacticInfo
  | .context _ t              => hasTacticInfo t
  | _                         => false

/--
Returns `true` when `before` and `after` are equal as multisets. This single
check subsumes pure no-ops (`skip`, `sleep_heartbeats`, `#adaptation_note`)
and pure reorderings (`swap`, `rotate_left`, `rotate_right`, `pick_goal`,
`swap_var`).
-/
def isReorderOrNoop (before after : List MVarId) : Bool :=
  before.length == after.length && before.all after.contains

/--
Walks an `InfoTree` and collects the offending tactic invocations as
`(stx, #goalsBefore, #goalsAfter, #unaffectedGoals)`.
-/
partial def collectMultiGoal (env : Environment) (safe : Std.HashSet SyntaxNodeKind) :
    InfoTree → Array (Syntax × Nat × Nat × Nat)
  | .node info args =>
    let descend := (args.toArray.map (collectMultiGoal env safe)).flatten
    match info with
    | .ofTacticInfo ti =>
      -- Structural node: real work is in a descendant `TacticInfo`.
      if args.any hasTacticInfo then descend
      -- Already focused on a single goal: nothing to lint.
      else if ti.goalsBefore.length ≤ 1 then descend
      -- Pure reorder or no-op.
      else if isReorderOrNoop ti.goalsBefore ti.goalsAfter then descend
      -- Not a real tactic-category node (parser token, sequence shell, ...).
      else if !isTacticKind env ti.stx.getKind then descend
      -- Explicitly whitelisted.
      else if safe.contains ti.stx.getKind then descend
      else match ti.stx.getHeadInfo with
        | .original .. =>
          -- Goals that survive untouched from before to after.
          let background := ti.goalsAfter.filter ti.goalsBefore.contains
          if background.isEmpty then descend
          else descend.push
            (ti.stx, ti.goalsBefore.length, ti.goalsAfter.length, background.length)
        | _ => descend
    | _ => descend
  | .context _ t => collectMultiGoal env safe t
  | _ => #[]

@[inherit_doc linter.extra.multiGoal]
def multiGoalLinter : Linter where run := withSetOptionIn fun _stx => do
  unless getLinterValueExtra linter.extra.multiGoal (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let env  ← getEnv
  let safe := multiGoalSafeExt.getState env
  for t in (← getInfoTrees) do
    for (stx, before, after, n) in collectMultiGoal env safe t do
      let goals (k : Nat) := if k == 1 then m!"1 goal" else m!"{k} goals"
      let pretty ← liftCoreM <|
        try PrettyPrinter.ppTactic ⟨stx⟩
        catch _ => pure f!"(failed to pretty print)"
      logLintIfExtra linter.extra.multiGoal stx m!"\
        The following tactic starts with {goals before} and ends with {goals after}, \
        {n} of which {if n == 1 then "is" else "are"} not operated on:\
        {indentD pretty}\n\
        Please focus on the current goal, e.g. with `·` (typed as `\\.`)."

builtin_initialize addLinter multiGoalLinter

end Lean.Linter.Extra
