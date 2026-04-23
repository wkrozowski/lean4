module
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Sym.Simp.Attr
import Lean.Meta.Sym.Simp.Simproc
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.AppBuilder

namespace Homomorphism

open Lean Meta Grind Sym Simp

initialize registerTraceClass `homo
initialize registerTraceClass `homo.visit

/--
Declares attribute `[grind_mono]` for marking theorems implementing the homomorphism.
-/
initialize homoSimpExtension : SymSimpExtension ←
  registerSymSimpAttr `grind_homo "`grind` homomorphism attribute"

/--
Returns theorems marked with `[grind_mono]`
-/
def getTheorems : CoreM Theorems :=
  homoSimpExtension.getTheorems

/--
Creates a simproc that applies the theorems marked with `[grind_mono]`.
This simproc is meant to be applied as a `pre` method.

Recall that `grind` internalizes terms bottom-up. By the time a
simplification set runs on a term `e`, all subterms of `e` are already
in the E-graph and have been processed by the pipeline.

**Stop condition.** When simp encounters a term `t` during traversal:

- If a rule matches `t`: apply it, continue (result is a new term).
- If no rule matches `t` AND `t` is already in the E-graph:
  stop, don't descend. Otherwise: descend normally.
-/
def mkRewriter : GoalM Sym.Simp.Simproc := do
  let s ← get
  -- Remark: We are not using any discharger. So, our rewriting rules are all context
  -- independent.
  let rw := (← getTheorems).rewrite
  return fun e => do
    trace[homo.visit] "{e}"
    let r ← rw e
    if !r.isRfl then return r
    -- If `e` is already in the E-graph, we don't revisit its children
    let done := s.enodeMap.contains { expr := e }
    return .rfl (done := done)

structure State where
  cache : Sym.Simp.Cache := {}

initialize homoExt : SolverExtension Sym.Simp.Cache ←
  registerSolverExtension (return {})

/-- Apply the homomorphism theorems. -/
def applyHomo (e : Expr) : GoalM Sym.Simp.Result := do
  let methods := { pre := (← mkRewriter) }
  -- Reuse cache.
  let persistentCache ← homoExt.getState
  homoExt.modifyState fun _ => {} -- Improve uniqueness. This is a minor optimization
  let (r, s) ← Sym.Simp.SimpM.run (Sym.Simp.simp e) (methods := methods) (s := { persistentCache })
  homoExt.modifyState fun _ => s.persistentCache
  return r

/--
Returns `true` if some theorem marked with `[grind_homo]` is applicable to `e`.

Motivation: we don't want to start the simplifier and fail immediately.
-/
def isTarget (e : Expr) : CoreM Bool := do
  let thms ← getTheorems
  return !(thms.getMatch e).isEmpty

/--
Internalization procedure for this module. See `homoExt.setMethods`
-/
def internalize (e : Expr) (_ : Option Expr) : GoalM Unit := do
  unless (← isTarget e) do return ()
  let .step e₁ h₁ _ ← applyHomo e | return ()
  let r ← preprocess e₁
  let h ← mkEqTrans h₁ (← r.getProof)
  let gen ← getGeneration e
  Grind.internalize r.expr gen
  trace[homo] "{e}\n====>\n{r.expr}"
  pushEq e r.expr h

initialize
  homoExt.setMethods
    (internalize := internalize)

end Homomorphism
