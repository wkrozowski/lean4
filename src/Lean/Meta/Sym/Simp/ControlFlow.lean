/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.Simp.App
import Lean.Meta.SynthInstance
import Lean.Meta.WHNF
import Lean.Meta.Match.MatchEqsExt
import Lean.Meta.AppBuilder
import Init.Sym.Lemmas
import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.Discharger
namespace Lean.Meta.Sym.Simp
open Internal

/--
Simplifies a non-dependent `if-then-else` expression.
-/
def simpIte : Simproc := fun e => do
  let numArgs := e.getAppNumArgs
  if numArgs < 5 then return .rfl (done := true)
  propagateOverApplied e (numArgs - 5) fun e => do
    let_expr f@ite α c _ a b := e | return .rfl
    match (← simp c) with
    | .rfl _ =>
      if isSameExpr c (← getTrueExpr) then
        return .step a <| mkApp3 (mkConst ``ite_true f.constLevels!) α a b
      else if isSameExpr c (← getFalseExpr) then
        return .step b <| mkApp3 (mkConst ``ite_false f.constLevels!) α a b
      else
        return .rfl (done := true)
    | .step c' h _ =>
      if isSameExpr c' (← getTrueExpr) then
        return .step a <| mkApp (e.replaceFn ``ite_cond_eq_true) h
      else if isSameExpr c' (← getFalseExpr) then
        return .step b <| mkApp (e.replaceFn ``ite_cond_eq_false) h
      else
        let .some inst' ← trySynthInstance (mkApp (mkConst ``Decidable) c') | return .rfl
        let inst' ← shareCommon inst'
        let e' := e.getBoundedAppFn 4
        let e' ← mkAppS₄ e' c' inst' a b
        let h' := mkApp3 (e.replaceFn ``Sym.ite_cond_congr) c' inst' h
        return .step e' h' (done := true)

/--
Simplifies a dependent `if-then-else` expression.
-/
def simpDIte : Simproc := fun e => do
  let numArgs := e.getAppNumArgs
  if numArgs < 5 then return .rfl (done := true)
  propagateOverApplied e (numArgs - 5) fun e => do
    let_expr f@dite α c _ a b := e | return .rfl
    match (← simp c) with
    | .rfl _ =>
      if isSameExpr c (← getTrueExpr) then
        let a' ← share <| a.betaRev #[mkConst ``True.intro]
        return .step a' <| mkApp3 (mkConst ``dite_true f.constLevels!) α a b
      else if isSameExpr c (← getFalseExpr) then
        let b' ← share <| b.betaRev #[mkConst ``not_false]
        return .step b' <| mkApp3 (mkConst ``dite_false f.constLevels!) α a b
      else
        return .rfl (done := true)
    | .step c' h _ =>
      if isSameExpr c' (← getTrueExpr) then
        let h' ← shareCommon <| mkOfEqTrueCore c h
        let a ← share <| a.betaRev #[h']
        return .step a <| mkApp (e.replaceFn ``dite_cond_eq_true) h
      else if isSameExpr c' (← getFalseExpr) then
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
        return .step e' h' (done := true)

/--
Simplifies a `cond` expression (aka Boolean `if-then-else`).
-/
def simpCond : Simproc := fun e => do
  let numArgs := e.getAppNumArgs
  if numArgs < 4 then return .rfl (done := true)
  propagateOverApplied e (numArgs - 4) fun e => do
    let_expr f@cond α c a b := e | return .rfl
    match (← simp c) with
    | .rfl _ =>
      if isSameExpr c (← getBoolTrueExpr) then
        return .step a <| mkApp3 (mkConst ``cond_true f.constLevels!) α a b
      else if isSameExpr c (← getBoolFalseExpr) then
        return .step b <| mkApp3 (mkConst ``cond_false f.constLevels!) α a b
      else
        return .rfl (done := true)
    | .step c' h _ =>
      if isSameExpr c' (← getBoolTrueExpr) then
        return .step a <| mkApp (e.replaceFn ``Sym.cond_cond_eq_true) h
      else if isSameExpr c' (← getBoolFalseExpr) then
        return .step b <| mkApp (e.replaceFn ``Sym.cond_cond_eq_false) h
      else
        let e' := e.getBoundedAppFn 3
        let e' ← mkAppS₃ e' c' a b
        let h' := mkApp2 (e.replaceFn ``Sym.cond_cond_congr) c' h
        return .step e' h' (done := true)

/--
Simplifies a `match`-expression.
-/
def simpMatch (declName : Name) : Simproc := fun e => do
  if let some e' ← reduceRecMatcher? e then
    return .step e' (← mkEqRefl e')
  let some info ← getMatcherInfo? declName
    | return .rfl
  -- **Note**: Simplify only the discriminants
  let start := info.numParams + 1
  let stop  := start + info.numDiscrs
  let r ← simpAppArgRange e start stop
  match r with
  | .step .. => return r
  | _ => return .rfl (done := true)

def getMatchTheorems (declName : Name) : SimpM (Array Theorem) := do
  let state ← get
  if state.matcherCache.contains declName then
    return state.matcherCache.find! declName
  else
    let congrEqns ← Match.genMatchCongrEqns declName
    let theorems : Array Theorem ← congrEqns.mapM (do mkHEqTheoremFromDecl ·)
    modify (fun oldState => {oldState with matcherCache := oldState.matcherCache.insert declName theorems})
    return theorems

def simpMatch' (declName : Name) : Simproc := fun e => do
  unless ← isMatcherApp e do
    return .rfl
  -- **Note**: Simplify only the discriminants

  let theorems : Array Theorem ← getMatchTheorems declName
  for thm in theorems do
    let res ← Theorem.rewriteMatchCongrThm thm e (d := dischargeSimpCbv) (heq := true)
    match res with
    | .step e' proof _ =>
      trace[Meta.Tactic] "Obtained: {e'} with proof: {proof}"
      return res
    | .rfl done =>
      if !done then
        continue
      else
        return .rfl (done := true)
  return .rfl
/--
Simplifies control-flow expressions such as `if-then-else` and `match` expressions.
It visits only the conditions and discriminants.
-/
public def simpControl : Simproc := fun e => do
  if !e.isApp then return .rfl
  let .const declName _ := e.getAppFn | return .rfl
  if declName == ``ite then
    simpIte e
  else if declName == ``cond then
    simpCond e
  else if declName == ``dite then
    simpDIte e
  else
    simpMatch declName e

end Lean.Meta.Sym.Simp
