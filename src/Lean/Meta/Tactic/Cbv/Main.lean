/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude

public import Lean.Meta.Sym.Simp
import Lean.Meta.Eqns
import Lean.Meta.AppBuilder
import Lean.Meta.Sym.LitValues
import Lean.Meta.Match.MatchEqsExt
open Lean.Meta.Sym.Simp
namespace Lean.Meta.Tactic.Cbv


def isValueOf (toValue? : Expr → Option α) : Simproc := fun e =>
  return .rfl (toValue? e).isSome

-- Todo: recognise more values
abbrev isNatValue : Simproc := isValueOf Sym.getNatValue?
abbrev isStringValue : Simproc := isValueOf Sym.getStringValue?
abbrev isIntValue : Simproc := isValueOf Sym.getIntValue?

def isBuiltinValue : Simproc :=
  isNatValue <|> isIntValue

def betaReduce : Simproc := fun e => do
  -- TODO: Check if we can do term sharing here?
  let new := e.headBeta
  return .step new (← Sym.mkEqRefl new)

/--
  Precondition: We are dealing with a constant application, all arguments are evaluated
  Tries to apply equations obtained from an equation compiler
-/
def tryEquations : Simproc := fun e => do
  let some appFn := e.getAppFn.constName? | return .rfl
  let some eqnNames ← getEqnsFor? appFn | return .rfl
  let thms := Theorems.insertMany {} <| ← eqnNames.mapM (do mkTheoremFromDecl ·)
  thms.rewrite (d := dischargeNone) e

/-
  Precondition: We are dealing with a constant application, all arguments are evaluated, using equations from equations compiler failed
-/
def tryUnfold : Simproc := fun e => do
  let some appFn := e.getAppFn.constName? | return .rfl
  let some unfoldEqn ← getUnfoldEqnFor? appFn (nonRec := true) | return .rfl
  let thm ← mkTheoremFromDecl unfoldEqn
  Theorem.rewrite thm e

/-
  Precondition: We are dealing with an application to a matcher, discriminators are evaluated
-/
def tryMatchEquations (appFn : Name) : Simproc := fun e => do
  let eqnNames ← Match.getEquationsFor appFn
  let eqnNames := eqnNames.eqnNames
  let thms := Theorems.insertMany {} <| ← eqnNames.mapM (do mkTheoremFromDecl ·)
  thms.rewrite (d := dischargeNone) e

/-
  Tries to perform definitional matcher/rec/quot reduction. It is costly in the kernel.
-/
def reduceRecMatcher : Simproc := fun e => do
  if let some e' ← reduceRecMatcher? e then
    return .step e' (← Sym.mkEqRefl e')
  else
    return .rfl

/-
  Precondition: We are dealing with an application to a constant
-/
def tryMatcher : Simproc := fun e => do
  let some appFn := e.getAppFn.constName? | return .rfl
  let some info ← getMatcherInfo? appFn | return .rfl
  let start := info.numParams + 1
  let stop  := start + info.numDiscrs
  (simpAppArgRange · start stop)
    >> tryMatchEquations appFn
      <|> reduceRecMatcher
        <| e

/-
  Handles an application
-/
def cbvApp : Simproc := fun e => do
  unless e.isApp do return .rfl
  let fn := e.getAppFn
  if fn.isLambda then
    simpAppArgs >>
      betaReduce
        <| e
  else
    if (fn.isConst) then
      tryMatcher
        <|> simpAppArgs
            >> evalGround
              <|> tryEquations
              <|> tryUnfold -- possibly check if it is under applied
              <|> reduceRecMatcher
                <| e
    else
      let res ← simp fn
      match res with
      | .rfl _ => return .rfl
      | .step e' proof _ =>
        let newType ← Sym.inferType e'
        let congrArgFun ← withLocalDeclD `x newType fun x =>
          mkLambdaFVars #[x] <| mkAppN x e.getAppArgs
        let newValue := mkAppN e' e.getAppArgs
        let newProof ← mkCongrArg congrArgFun proof
        return .step newValue newProof

def handleProj (typeName : Name) (idx : Nat) (struct : Expr) : SimpM Result := do
  let res ← simp struct
  match res with
  | .rfl _ =>
    let some reduced ← reduceProj? <| Expr.proj typeName idx struct | do
      return .rfl
    return .step reduced (← Sym.mkEqRefl reduced)
  | .step e' proof _ =>
    let type ← Sym.inferType e'
    let congrArgFun ← withLocalDeclD `x type fun x => do
      mkLambdaFVars #[x] <| Expr.proj typeName idx x
    let newProof ← mkCongrArg congrArgFun proof
    -- TODO: check if I should use: Sym.mkProjS
    return .step (mkProj typeName idx e') newProof

def foldLit : Simproc := fun e => do
 let some n := e.rawNatLit? | return .rfl
 return .step (mkNatLit n) (← Sym.mkEqRefl e)

def cbvStep : Simproc := fun e => do
  match e with
  | .lit _ => foldLit e
  | .sort _ | .bvar _ | .const .. | .fvar _  | .mvar _ | .lam .. | .forallE .. => return .rfl
  | .proj typeName idx struct => handleProj typeName idx struct
  | .mdata m b => simpMData m b
  | .letE .. =>
    -- Does not seem to work properly yet
    simpLet e
  | .app .. => cbvApp e

def foldZero : Simproc := fun e => do
  if e.isConstOf ``Nat.zero then
    -- replace it with symbolic zero
    return .step (mkNatLit 0) (← Sym.mkEqRefl e) (done := true)
  else
    return .rfl

def cbvMain : Simproc := isBuiltinValue >> cbvStep

public def cbvEntry (e : Expr) : MetaM Result := do
  -- TODO: add preprocessing
  Sym.SymM.run <| Sym.Simp.SimpM.run' (simp e) (methods := { step := cbvMain, post := foldZero })

end Lean.Meta.Tactic.Cbv
