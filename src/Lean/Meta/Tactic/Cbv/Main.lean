/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude

public import Lean.Meta.Sym.Simp
public import Std.Data.DHashMap.Lemmas
import Lean.Meta.Eqns
import Lean.Meta.AppBuilder
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.LitValues
import Lean.Meta.Match.MatchEqsExt
import Lean.Meta.Sym.Simp.Have
import Lean.Meta.Tactic.Cbv.TheoremsCache
import Lean.Meta.Sym.Util
open Lean.Meta.Sym.Simp
namespace Lean.Meta.Tactic.Cbv


def isValueOf (toValue? : Expr → Option α) : Simproc := fun e =>
  return .rfl (toValue? e).isSome

-- Todo: recognise more values
abbrev isNatValue : Simproc := isValueOf Sym.getNatValue?
abbrev isStringValue : Simproc := isValueOf Sym.getStringValue?
abbrev isIntValue : Simproc := isValueOf Sym.getIntValue?
abbrev isBitVecValue : Simproc := isValueOf Sym.getBitVecValue?
abbrev isFinValue : Simproc := isValueOf Sym.getFinValue?
abbrev isCharValue : Simproc := isValueOf Sym.getCharValue?

def isBuiltinValue : Simproc :=
      isNatValue
  <|> isIntValue
  <|> isBitVecValue
  <|> isStringValue
  <|> isFinValue
  <|> isCharValue

/- Possibly make this public? -/
private def isAlwaysZero : Level → Bool
  | .zero ..    => true
  | .mvar ..    => false
  | .param ..   => false
  | .succ ..    => false
  | .max u v    => isAlwaysZero u && isAlwaysZero v
  | .imax _ u   => isAlwaysZero u

/- Modified for the SymM usage -/
def isProp (e : Expr) : Sym.SymM Bool := do
  match (← isPropQuick e) with
  | .true  => return true
  | .false => return false
  | .undef =>
    let type ← Sym.inferType e
    let type ← whnfD type
    match type with
    | Expr.sort u => return isAlwaysZero (← instantiateLevelMVars u)
    | _           => return false

def isProof (e : Expr) : Sym.SymM Bool := do
  match (← isProofQuick e) with
  | .true  => return true
  | .false => return false
  | .undef => isProp (← Sym.inferType e)

def doneIfProof : Simproc := fun e => do
  let val ← isProof e
  return .rfl val

def logWarningAndFail (msg : MessageData) : Simproc := fun _ => do
  logWarning msg
  return .rfl (done := true)

def betaReduce : Simproc := fun e => do
  -- TODO: Check if we are doing term sharing correctly here.
  let new := e.headBeta
  let new ← Sym.share new
  return .step new (← Sym.mkEqRefl new)

/--
  Precondition: We are dealing with a constant application, all arguments are evaluated
  Tries to apply equations obtained from an equation compiler
-/
def tryEquations : Simproc := fun e => do
  let some appFn := e.getAppFn.constName? | return .rfl
  let thms ← getEqnTheorems appFn
  thms.rewrite (d := dischargeNone) e

def tryUserTheorems : Simproc := fun e => do
  let thms ← getUserTheorems
  thms.rewrite (d := dischargeNone) e

/-
  Precondition: We are dealing with a constant application, all arguments are evaluated, using equations from equations compiler failed
-/
def tryUnfold : Simproc := fun e => do
  let some appFn := e.getAppFn.constName? | return .rfl
  let some thm ← getUnfoldTheorem appFn | return .rfl
  Theorem.rewrite thm e

/-
  Precondition: We are dealing with an application to a matcher, discriminators are evaluated
-/
def tryMatchEquations (appFn : Name) : Simproc := fun e => do
  let thms ← getMatchTheorems appFn
  thms.rewrite (d := dischargeNone) e

/-
  Tries to perform definitional matcher/rec/quot reduction. It is costly in the kernel.
-/
def reduceRecMatcher : Simproc := fun e => do
  if let some e' ← reduceRecMatcher? e then
    return .step e' (← Sym.mkEqRefl e')
  else
    return .rfl

def matcherWarning (info : MatcherInfo) : Simproc := fun e => do
  if (info.arity <= e.getAppArgs.size) then
    logWarning m!"Cannot reduce matcher application {e}"
    return .rfl true
  else
    return .rfl false

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
      -- This one is for debugging purposes
      <|> matcherWarning info
        <| e

-- Possibly no need for this
def constructorApplication : Simproc := fun e => do
  let fn := e.getAppFn
  let some fnName := fn.constName? | return .rfl
  let constInfo ← getConstInfo fnName
  return .rfl constInfo.isCtor

def mkCongrArgS (f : Expr) (h : Expr) : Sym.SymM Expr := do
  let fType ← Sym.inferType f
  let hType ← Sym.inferType h
  match fType.arrow?, hType.eq? with
  | some (α, β), some (_, a, b) =>
      let u ← Sym.getLevel α
      let v ← Sym.getLevel β
      return mkApp6 (mkConst ``congrArg [u, v]) α β a b f h
  | _, _ => throwError "Failed constructing a `congrArg` proof"

def checkIfForbidden : Simproc := fun e => do
  let isForbidden ← isForbidden e.getAppFn.constName!
  return .rfl <| isForbidden

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
      tryMatcher <|> simpControl'
        <|> simpAppArgs
              <|> tryUserTheorems
            >>    checkIfForbidden
              <|> evalGround
              -- Possibly check here if it is underapplied
              <|> tryEquations
              <|> tryUnfold
              <|> reduceRecMatcher
                 <| e
    else
      let res ← simp fn
      match res with
      | .rfl _ => return res
      | .step e' proof _ =>
        let newType ← Sym.inferType e'
        let congrArgFun := Lean.mkLambda `x .default newType (mkAppN (.bvar 0) e.getAppArgs)
        let newValue ← Sym.Internal.mkAppSN e' e.getAppArgs
        let newProof ← mkCongrArg congrArgFun proof
        return .step newValue newProof

def handleProj (typeName : Name) (idx : Nat) (struct : Expr) (e : Expr) : SimpM Result := do
  let res ← simp struct
  match res with
  | .rfl _ =>
    let some reduced ← reduceProj? <| .proj typeName idx struct | do
      return .rfl

    let reduced ← Sym.share reduced
    return .step reduced (← Sym.mkEqRefl reduced)
  | .step e' proof _ =>
    let type ← Sym.inferType e'
    let congrArgFun := Lean.mkLambda `x .default type <| .proj typeName idx <| .bvar 0

    let newProof ← mkCongrArg congrArgFun proof
    return .step (← Lean.Expr.updateProjS! e e') newProof

def foldLit : Simproc := fun e => do
 let some n := e.rawNatLit? | return .rfl
 -- Do we need sharing here?
 return .step (mkNatLit n) (← Sym.mkEqRefl e)

def zetaReduce : Simproc := fun e => do
  let .letE _ _ value body _ := e | return .rfl
  let new := expandLet body #[value]
  -- Re-establishing the invariant might be pricy
  let new ← Sym.share new
  return .step new (← Sym.mkEqRefl new)

def handleConst (n : Name) : Simproc := fun e => do
  let info ← getConstInfo n
  -- if ← Meta.isInstance n then return .rfl
  unless info.isDefinition do
    return .rfl
  let eType ← Sym.inferType e
  let eType ← whnfD eType
  unless eType matches .forallE .. do
    return .rfl
  let some thm ← getUnfoldTheorem n | return .rfl
  Theorem.rewrite thm e

def cbvStep : Simproc := fun e => do
  match e with
  | .lit _ =>
    foldLit e
  | .const n _ => handleConst n <| e
  | .sort _ | .bvar _ | .fvar _  | .mvar _ | .lam .. | .forallE .. => return .rfl
  | .proj typeName idx struct => handleProj typeName idx struct e
  | .mdata m b => simpMData m b
  | .letE .. =>
    -- This might be inefficient
    (simpLet >> zetaReduce) e
  | .app .. => cbvApp e

def foldZero : Simproc := fun e => do
  if e.isConstOf ``Nat.zero then
    -- replace it with symbolic zero
    return .step (← Sym.getNatZeroExpr) (← Sym.mkEqRefl e) (done := true)
  else
    return .rfl

public def cbvEntry (e : Expr) : MetaM Result := do
  addDoNotUnfold ``Std.DHashMap.emptyWithCapacity
  addDoNotUnfold ``Std.DHashMap.contains
  addDoNotUnfold ``Std.DHashMap.insert
  addDoNotUnfold ``Std.DHashMap.insertIfNew
  addDoNotUnfold ``WellFounded.extrinsicFix₂
  addDoNotUnfold ``List.iter
  addUserTheoremFromDecl ``Std.DHashMap.contains_insert
  addUserTheoremFromDecl ``Std.DHashMap.contains_insertIfNew
  addUserTheoremFromDecl ``Std.DHashMap.contains_emptyWithCapacity
  addUserTheoremFromDecl ``Bool.false_eq_true
  addUserTheoremFromDecl ``List.toArray_iter

  let e ← Sym.unfoldReducible e
  Sym.SymM.run do
    let e ← Sym.shareCommon e
    Sym.Simp.SimpM.run' (simp e) (methods := {pre := doneIfProof >> isBuiltinValue, step := cbvStep, post := foldZero })

end Lean.Meta.Tactic.Cbv
