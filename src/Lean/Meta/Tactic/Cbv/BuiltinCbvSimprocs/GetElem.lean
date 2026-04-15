/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module
prelude
import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.Simp.Rewrite
import Init.CbvSimproc
import Lean.Meta.Tactic.Cbv.CbvSimproc
import Lean.Meta.Tactic.Cbv.CbvEvalExt

/-!
# GetElem cbv simproc

Custom cbv simproc for `GetElem.getElem` that bypasses the discrimination tree.

The standard `@[cbv_eval]` mechanism fails for `GetElem.getElem` because the
`Sym.Simp.DiscrTree` does not eta-reduce subexpressions during pattern insertion,
but does eta-reduce during matching. The `dom` argument (e.g.,
`fun m a => Membership.mem m a`) stays as a lambda in the pattern (key `.other`)
but is eta-reduced to a partial application in the expression (key `.const`),
causing the discrimination tree lookup to return zero matches.

This simproc matches any `GetElem.getElem` application using an all-wildcard
pattern, then manually tries each `@[cbv_eval]` theorem registered for
`GetElem.getElem` via `Theorem.rewrite` (which uses full unification).
-/

namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp

/--
Try all `@[cbv_eval]` theorems registered for `GetElem.getElem` by calling
`Theorem.rewrite` on each one. This bypasses the discrimination tree lookup
that would otherwise fail due to the eta-reduction asymmetry.
-/
builtin_cbv_simproc cbv_eval simpGetElem (@GetElem.getElem _ _ _ _ _ _ _ _) := fun e => do
  let s := cbvEvalExt.getState (← getEnv)
  let entries := (s.entries.find? ``GetElem.getElem).getD #[]
  for entry in entries do
    let result ← Simproc.tryCatch (entry.thm.rewrite · dischargeNone) e
    if !result.isRfl then
      trace[Meta.Tactic.cbv.rewrite] "@[cbv_eval] `GetElem.getElem`:{indentExpr e}\n==>{indentExpr (result.getResultExpr e)}"
      return result
  return .rfl

end Lean.Meta.Tactic.Cbv
