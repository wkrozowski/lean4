/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.AppBuilder
import Lean.Meta.Sym.Simp.Result
import Lean.Meta.Sym.Simp.Simproc
import Lean.Meta.Sym.Simp.App
import Lean.Meta.Sym.Simp.Have
import Lean.Meta.Sym.Simp.Lambda
import Lean.Meta.Sym.Simp.Forall
import Lean.Meta.WHNF
namespace Lean.Meta.Sym.Simp
open Internal

def reduceLambda : Simproc := fun e => do
  unless e.isApp do
    return Result.rfl
  unless e.getAppFn.isLambda do
    return Result.rfl
  let new := e.headBeta
  return (Result.step new (←mkEqRefl new))

def simpStep : Simproc := fun e => do
  match e with
  | .lit _ | .sort _ | .bvar _ | .const .. | .fvar _  | .mvar _ => return .rfl
  | .proj typeName idx struct =>
      let res ← simp struct
      match res with
      | .rfl .. =>
        let some e ← reduceProj? e | return .rfl
        return .step e (← mkEqRefl e) (done := true)
      | .step _ proof _ =>
        if let some e ← reduceProj? e then
          let res ← simp e
          return res
        let fType ← inferType struct
        let congrArgFun ← withLocalDecl (← mkFreshUserName `x) BinderInfo.default fType fun var => do
          let theoremLhs := Expr.proj typeName idx var
          mkLambdaFVars #[var] theoremLhs
        let congrArg ← mkCongrArg congrArgFun proof
        let some reduced ← reduceProj? congrArg | return .step congrArg proof (done := true)
        return .step reduced proof
  | .mdata m b =>
    let r ← simp b
    match r with
    | .rfl _ => return .rfl
    | .step b' h _ => return .step (← mkMDataS m b') h
  | .lam .. => simpLambda e
  | .forallE .. => simpForall e
  | .letE .. => simpLet e
  | .app .. =>
      (simpAppArgs >> reduceLambda) e




abbrev cacheResult (e : Expr) (r : Result) : SimpM Result := do
  modify fun s => { s with cache := s.cache.insert { expr := e } r }
  return r

@[export lean_sym_simp]
def simpImpl (e₁ : Expr) : SimpM Result := withIncRecDepth do
  trace[Meta.Tactic] "Called simp with {e₁}"
  let numSteps := (← get).numSteps
  if numSteps >= (← getConfig).maxSteps then
    throwError "`simp` failed: maximum number of steps exceeded"
  if let some result := (← getCache).find? { expr := e₁ } then
    return result
  let numSteps := numSteps + 1
  if numSteps % 1000 == 0 then
    checkSystem "simp"
  modify fun s => { s with numSteps }
  let r₁ ← pre e₁
  match r₁ with
  | .rfl true | .step _ _ true => cacheResult e₁ r₁
  | .step e₂ h₁ false =>
    trace[Meta.Tactic] "Obtained {e₂} in pre"
    cacheResult e₁ (← mkEqTransResult e₁ e₂ h₁ (← simp e₂))
  | .rfl false =>
  let r₂ ← (simpStep >> post) e₁
  match r₂ with
  | .rfl _ | .step _ _ true => cacheResult e₁ r₂
  | .step e₂ h₁ false =>
    trace[Meta.Tactic] "Obtained {e₂} in post"
    cacheResult e₁ (← mkEqTransResult e₁ e₂ h₁ (← simp e₂))

end Lean.Meta.Sym.Simp
