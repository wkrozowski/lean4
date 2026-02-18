/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.Simp.Result
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.ControlFlow
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.Simp.App
import Lean.Meta.SynthInstance
import Lean.Meta.WHNF
import Lean.Meta.AppBuilder
import Init.Sym.Lemmas
import Lean.Meta.Tactic.Cbv.TheoremsLookup
/-!
# Control Flow Reduction for `cbv`

Handles `ite`, `dite`, `cond`, `Decidable.rec`, and matcher applications.

The strategy for `ite`/`dite` is non-contextual: only the condition is simplified, and if it
reduces to `True`/`False`, the appropriate branch is taken. When the condition doesn't reduce
directly but its `Decidable` instance evaluates to a boolean, we go through `eq_true_of_decide`
/ `eq_false_of_decide` to recover a propositional proof. If the condition remains symbolic,
we rebuild the `ite`/`dite` with the simplified condition and a fresh `Decidable` instance.

This avoids the standard `ite_congr` approach which adds hypotheses to each branch,
invalidating the cache and causing exponential behavior on nested conditionals.
-/

namespace Lean.Meta.Sym.Simp
open Internal

/--
Simplify `ite c a b`. Only the condition `c` is simplified; branches are not entered unless
the condition resolves. Handles over-applied `ite` (extra arguments beyond the standard 5)
via `propagateOverApplied`.
-/
public def simpIteCbv : Simproc := fun e => do
  let numArgs := e.getAppNumArgs
  if numArgs < 5 then return .rfl (done := true)
  propagateOverApplied e (numArgs - 5) fun e => do
    let_expr f@ite α c _ a b := e | return .rfl
    match (← simp c) with
    | .rfl _ =>
      if (← isTrueExpr c) then
        return .step a <| mkApp3 (mkConst ``ite_true f.constLevels!) α a b
      else if (← isFalseExpr  c) then
        return .step b <| mkApp3 (mkConst ``ite_false f.constLevels!) α a b
      else
        let .some inst' ← trySynthInstance (mkApp (mkConst ``Decidable) c) | return .rfl
        let inst' ← shareCommon inst'
        let toEval ← mkAppS₂ (mkConst ``Decidable.decide) c inst'
        let evalRes ← simp toEval
        match evalRes with
        | .rfl _ =>
          return .rfl (done := true)
        | .step v hv _ =>
          if (← isBoolTrueExpr v) then
            let h' := mkApp3 (mkConst ``eq_true_of_decide) c inst' hv
            let inst' := mkConst ``instDecidableTrue
            let c' ← getTrueExpr
            let e' := e.getBoundedAppFn 4
            let e' ← mkAppS₄ e' c' inst' a b
            let h' := mkApp3 (e.replaceFn ``Sym.ite_cond_congr) c' inst' h'
            let ha := mkApp3 (mkConst ``ite_true f.constLevels!) α a b
            let ha ← mkEqTrans e e' h' a ha
            return .step a ha (done := false)
          else if  (← isBoolFalseExpr v)  then
            let h' := mkApp3 (mkConst ``eq_false_of_decide) c inst' hv
            let inst' := mkConst ``instDecidableFalse
            let c' ← getFalseExpr
            let e' := e.getBoundedAppFn 4
            let e' ← mkAppS₄ e' c' inst' a b
            let h' := mkApp3 (e.replaceFn ``Sym.ite_cond_congr) c' inst' h'
            let hb := mkApp3 (mkConst ``ite_false f.constLevels!) α a b
            let hb ← mkEqTrans e e' h' b hb
            return .step b hb (done := false)
          else
            return .rfl (done := true)
    | .step c' h _ =>
      if (← isTrueExpr c') then
        return .step a <| mkApp (e.replaceFn ``ite_cond_eq_true) h
      else if (← isFalseExpr c') then
        return .step b <| mkApp (e.replaceFn ``ite_cond_eq_false) h
      else
        let .some inst' ← trySynthInstance (mkApp (mkConst ``Decidable) c') | return .rfl
        let inst' ← shareCommon inst'
        let e' := e.getBoundedAppFn 4
        let e' ← mkAppS₄ e' c' inst' a b
        let h' := mkApp3 (e.replaceFn ``Sym.ite_cond_congr) c' inst' h
        return .step e' h'

/--
Simplify `dite c a b`. Same strategy as `simpIteCbv`, but branches receive a proof of the
condition (`h : c` or `h : ¬c`), so when the condition is rewritten we must transport the
proof via `Eq.mpr_prop` / `Eq.mpr_not`.
-/
public def simpDIteCbv : Simproc := fun e => do
  let numArgs := e.getAppNumArgs
  if numArgs < 5 then return .rfl (done := true)
  propagateOverApplied e (numArgs - 5) fun e => do
    let_expr f@dite α c _ a b := e | return .rfl
    match (← simp c) with
    | .rfl _ =>
      if (← isTrueExpr c) then
        let a' ← share <| a.betaRev #[mkConst ``True.intro]
        return .step a' <| mkApp3 (mkConst ``dite_true f.constLevels!) α a b
      else if (← isFalseExpr c) then
        let b' ← share <| b.betaRev #[mkConst ``not_false]
        return .step b' <| mkApp3 (mkConst ``dite_false f.constLevels!) α a b
      else
        let .some inst' ← trySynthInstance (mkApp (mkConst ``Decidable) c) | return .rfl
        let inst' ← shareCommon inst'
        let toEval ← mkAppS₂ (mkConst ``Decidable.decide) c inst'
        let evalRes ← simp toEval
        match evalRes with
        | .rfl _ => return .rfl (done := true)
        | .step v hv _ =>
          if  (← isBoolTrueExpr v) then
            let h' := mkApp3 (mkConst ``eq_true_of_decide) c inst' hv
            let inst' := mkConst ``instDecidableTrue
            let e' := e.getBoundedAppFn 4
            let h ← shareCommon h'
            let c' ← getTrueExpr
            let a ← share <| mkLambda `h .default c' (a.betaRev #[mkApp4 (mkConst ``Eq.mpr_prop) c c' h (mkBVar 0)])
            let b ← share <| mkLambda `h .default (mkNot c') (b.betaRev #[mkApp4 (mkConst ``Eq.mpr_not) c c' h (mkBVar 0)])
            let e' ← mkAppS₄ e' c' inst' a b
            let h' := mkApp3 (e.replaceFn ``Sym.dite_cond_congr) c' inst' h
            let a' ← share <| a.betaRev #[mkConst ``True.intro]
            let ha := mkApp3 (mkConst ``dite_true f.constLevels!) α a b
            let ha ← mkEqTrans e e' h' a' ha
            return .step a' ha
          else if  (← isBoolFalseExpr v)  then
            let h' := mkApp3 (mkConst ``eq_false_of_decide) c inst' hv
            let inst' := mkConst ``instDecidableFalse
            let e' := e.getBoundedAppFn 4
            let h ← shareCommon h'
            let c' ← getFalseExpr
            let a ← share <| mkLambda `h .default c' (a.betaRev #[mkApp4 (mkConst ``Eq.mpr_prop) c c' h (mkBVar 0)])
            let b ← share <| mkLambda `h .default (mkNot c') (b.betaRev #[mkApp4 (mkConst ``Eq.mpr_not) c c' h (mkBVar 0)])
            let e' ← mkAppS₄ e' c' inst' a b
            let h' := mkApp3 (e.replaceFn ``Sym.dite_cond_congr) c' inst' h
            let b' ← share <| b.betaRev #[mkConst ``not_false]
            let hb := mkApp3 (mkConst ``dite_false f.constLevels!) α a b
            let hb ← mkEqTrans e e' h' b' hb
            return .step b' hb
          else
            return .rfl (done := true)
    | .step c' h _ =>
      if (← isTrueExpr c') then
        let h' ← shareCommon <| mkOfEqTrueCore c h
        let a ← share <| a.betaRev #[h']
        return .step a <| mkApp (e.replaceFn ``dite_cond_eq_true) h
      else if (← isFalseExpr c') then
        let h' ← shareCommon <| mkOfEqFalseCore c h
        let b ← share <| b.betaRev #[h']
        return .step b <| mkApp (e.replaceFn ``dite_cond_eq_false) h
      else
        let .some inst' ← trySynthInstance (mkApp (mkConst ``Decidable) c') | return .rfl
        let inst' ← shareCommon inst'
        let e' := e.getBoundedAppFn 4
        let h ← shareCommon h
        let a ← share <| mkLambda `h .default c' (a.betaRev #[mkApp4 (mkConst ``Eq.mpr_prop) c c' h (mkBVar 0)])
        let b ← share <| mkLambda `h .default (mkNot c') (b.betaRev #[mkApp4 (mkConst ``Eq.mpr_not) c c' h (mkBVar 0)])
        let e' ← mkAppS₄ e' c' inst' a b
        let h' := mkApp3 (e.replaceFn ``Sym.dite_cond_congr) c' inst' h
        return .step e' h'

end Lean.Meta.Sym.Simp

namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp

def tryMatchEquations (appFn : Name) : Simproc := fun e => do
  let thms ← getMatchTheorems appFn
  thms.rewrite (d := dischargeNone) e

/-- Reduce recursor, matcher, and quotient applications via the kernel reducer. -/
public def reduceRecMatcher : Simproc := fun e => do
  if let some e' ← reduceRecMatcher? e then
    return .step e' (← Sym.mkEqRefl e')
  else
    return .rfl

def tryMatcher : Simproc := fun e => do
  unless e.isApp do
    return .rfl
  let some appFn := e.getAppFn.constName? | return .rfl
  let some info ← getMatcherInfo? appFn | return .rfl
  let start := info.numParams + 1
  let stop  := start + info.numDiscrs
  (simpAppArgRange · start stop)
    >> tryMatchEquations appFn
      <|> reduceRecMatcher
        <| e

/--
Dispatch control flow constructs. Precondition: `e` is an application.
Routes `ite`, `cond`, `dite` to their specialized handlers. For `Decidable.rec`, forces
simplification of the last arguments (the instance and discriminant) before reducing via
`reduceRecMatcher`. All other applications are routed to `tryMatcher`.
-/
public def simpControlCbv : Simproc := fun e => do
  let .const declName _ := e.getAppFn | return .rfl
  if declName == ``ite then
    simpIteCbv e
  else if declName == ``cond then
    simpCond e
  else if declName == ``dite then
    simpDIteCbv e
  else if declName == ``Decidable.rec then
    -- We force the rewrite in the last argument, so that we can unfold the `Decidable` instance.
    (simpInterlaced · #[false,false,true,true,true]) >> reduceRecMatcher <| e
  else
    tryMatcher e

end Lean.Meta.Tactic.Cbv
