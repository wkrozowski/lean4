/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Tactic.Cbv.Opaque
public import Lean.Meta.Tactic.Cbv.ControlFlow
import Lean.Meta.Tactic.Cbv.Util
import Lean.Meta.Tactic.Cbv.TheoremsLookup
import Lean.Meta.Tactic.Cbv.CbvEvalExt
import Lean.Meta.Sym
import Lean.Meta.Tactic.Refl

/-!
# Call-by-Value Reduction Tactic

The `cbv` tactic reduces expressions by call-by-value evaluation, producing kernel-checkable
equality proofs. It is built on top of `Sym.Simp`, a structural simplifier that uses hash-consing
and pointer-based caching for efficient normalization of large ground terms.

## Reduction Strategy

`cbv` normalizes expressions bottom-up: arguments are fully reduced before function bodies are
unfolded. This is implemented via `Sym.Simp`'s two-phase architecture:

- **Pre-phase** (`cbvPre`): Handles literals, projections, let-bindings, control flow (`ite`/`dite`),
  and recognizes terms that should not be reduced further (builtin values, proofs, opaque constants).
- **Post-phase** (`cbvPost`): Evaluates ground arithmetic/string operations via `evalGround`,
  and unfolds function applications using equation lemmas.

Since `Sym.Simp` recursively simplifies subterms between the pre and post phases, arguments are
normalized before the post-phase attempts to unfold the head function — giving call-by-value
behavior. `cbv` does not reduce under binders (lambdas, foralls).
-/

namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp

public register_builtin_option cbv.warning : Bool := {
  defValue := true
  descr    := "disable `cbv` usage warning"
}

def tryMatchEquations (appFn : Name) : Simproc := fun e => do
  let thms ← getMatchTheorems appFn
  thms.rewrite (d := dischargeNone) e

def tryEquations : Simproc := fun e => do
  unless e.isApp do
    return .rfl
  let some appFn := e.getAppFn.constName? | return .rfl
  let thms ← getEqnTheorems appFn
  thms.rewrite (d := dischargeNone) e

def tryUnfold : Simproc := fun e => do
  unless e.isApp do
    return .rfl
  let some appFn := e.getAppFn.constName? | return .rfl
  let some thm ← getUnfoldTheorem appFn | return .rfl
  Theorem.rewrite thm e

/--
Try reducing a matcher application. First simplifies the discriminants (the arguments in range
`[numParams + 1, numParams + 1 + numDiscrs)`), then attempts to apply the match equations.
Falls back to `reduceRecMatcher` if equation-based rewriting fails.
Simplifying discriminants can fail if they are dependent.
-/
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
Handle an application whose head is a constant. Skips constants marked with `@[cbv_opaque]`;
otherwise tries equation lemmas, then the unfold equation.
-/
def handleConstApp : Simproc := fun e => do
  if (← isCbvOpaque e.getAppFn.constName!) then
    return .rfl (done := true)
  else
    tryEquations <|> tryUnfold <| e

def betaReduce : Simproc := fun e => do
  -- TODO: Improve term sharing
  let new := e.headBeta
  let new ← Sym.share new
  return .step new (← Sym.mkEqRefl new)

def tryCbvTheorems : Simproc := fun e => do
  let some fnName := e.getAppFn.constName? | return .rfl
  let some evalLemmas ← getCbvEvalLemmas fnName | return .rfl
  Theorems.rewrite evalLemmas (d := dischargeNone) e

/--
Post-phase handler for applications. For constant-headed applications, tries `@[cbv_eval]`
theorems first, then equation lemmas (if the constant has a definition value), then
`reduceRecMatcher` as a fallback for recursor applications, quotients, etc.
For lambda-headed applications, beta-reduces.
-/
def handleApp : Simproc := fun e => do
  unless e.isApp do return .rfl
  let fn := e.getAppFn
  match fn with
  | .const constName _ =>
    let info ← getConstInfo constName
    tryCbvTheorems <|> (guardSimproc (fun _ => info.hasValue) handleConstApp) <|> reduceRecMatcher <| e
  | .lam .. => betaReduce e
  | _ => return .rfl

/--
Handle a bare constant (not applied). Tries `@[cbv_eval]` theorems if available,
otherwise skips constants marked with `@[cbv_opaque]`.
-/
def isOpaqueConst : Simproc := fun e => do
  let .const constName _ := e | return .rfl
  let hasTheorems := (← getCbvEvalLemmas constName).isSome
  if hasTheorems then
   let res ← (tryCbvTheorems) e
    match res with
    | .rfl false =>
      return .rfl
    | _ => return res
  else
    return .rfl (← isCbvOpaque constName)

def foldLit : Simproc := fun e => do
 let some n := e.rawNatLit? | return .rfl
 -- TODO: check performance of sharing
  return .step (← Sym.share <| mkNatLit n) (← Sym.mkEqRefl e)

/-- Zeta-reduce a dependent let-binding by substituting the value into the body.
Non-dependent let-bindings use `toBetaApp` instead (see `cbvPreStep`), which converts them
to function applications so that `Sym.Simp` can simplify the value before substitution. -/
def zetaReduce : Simproc := fun e => do
  let .letE _ _ value body _ := e | return .rfl
  let new := expandLet body #[value]
  -- TODO: Improve sharing
  let new ← Sym.share new
  return .step new (← Sym.mkEqRefl new)

/--
Reduce a projection `e.i`. First recursively simplifies the struct `e`, then tries to
reduce the projection. When the projection type is non-dependent, uses `congrArg` to
lift the equality proof. For dependent projections, falls back to `reduceProj?` or
heterogeneous congruence.
-/
def handleProj : Simproc := fun e => do
  let Expr.proj typeName idx struct := e | return .rfl
  -- We recursively simplify the projection
  let res ← simp struct
  match res with
  | .rfl _ =>
    let some reduced ← reduceProj? <| .proj typeName idx struct | do
      return .rfl (done := true)

    -- TODO: Figure if we can share this term incrementally
    let reduced ← Sym.share reduced
    return .step reduced (← Sym.mkEqRefl reduced)
  | .step e' proof _ =>
    let type ← Sym.inferType e'
    let congrArgFun := Lean.mkLambda `x .default type <| .proj typeName idx <| .bvar 0
    let congrArgFunType ← inferType congrArgFun
    -- If the type of a projection function is non-dependent, we can safely prove `e.i = e'.i` from `e = e'`
    if (congrArgFunType.isArrow) then
      let newProof ← mkCongrArg congrArgFun proof
      return .step (← Lean.Expr.updateProjS! e e') newProof
    else
      -- If the type of the projection function is dependent, we first try to reduce the projection
      let reduced ← reduceProj? e
      match reduced with
      | .some reduced =>
        let reduced ← Sym.share reduced
        return .step reduced (← Sym.mkEqRefl reduced)
      | .none =>
       -- If we failed to reduce it, we turn to a last resort; we try use heterogenous congruence lemma that we then try to turn into an equality.
        unless (← isDefEq struct e') do
          -- If we rewrote the projection body using something that holds up to propositional equality, then there is nothing we can do.
          -- TODO: Check if there is a need to report this to a user, or shall we fail silently.
          return .rfl
        let hcongr ← mkHCongr congrArgFun
        let newProof := mkApp3 (hcongr.proof) struct e' proof
        -- We have already checked if `struct` and `e'` are defEq, so we can skip the check.
        let newProof ← mkEqOfHEq newProof (check := false)
        return .step (← Lean.Expr.updateProjS! e e') newProof

/--
Simplify the head function of an application when it is not a lambda or constant
(e.g. a projection). Builds a congruence proof to propagate the rewrite.
-/
def simplifyAppFn : Simproc := fun e => do
    unless e.isApp do return .rfl
    let fn := e.getAppFn
    if fn.isLambda || fn.isConst then
      return .rfl
    else
    let res ← simp fn
    match (← simp fn) with
    | .rfl _ => return res
    | .step e' proof _ =>
      let newType ← Sym.inferType e'
      let congrArgFun := Lean.mkLambda `x .default newType (mkAppN (.bvar 0) e.getAppArgs)
      let newValue ← mkAppNS e' e.getAppArgs
      let newProof ← mkCongrArg congrArgFun proof
      return .step newValue newProof

/--
Unfold a bare constant that is a definition expecting arguments (type is a `forallE`).
Nullary definitions are skipped because their equation lemmas have no parameters to match,
and the goal-closing step in `cbvGoalCore` handles them via `isDefEq`.
-/
def handleConst : Simproc := fun e => do
  let .const n _ := e | return .rfl
  let info ← getConstInfo n
  unless info.isDefinition do return .rfl
  let eType ← Sym.inferType e
  let eType ← whnfD eType
  unless eType matches .forallE .. do
    return .rfl
  -- TODO: Check if we need to look if we applied all the levels correctly
  let some thm ← getUnfoldTheorem n | return .rfl
  Theorem.rewrite thm e

/--
Pre-phase dispatch on expression kind. Runs before `Sym.Simp` recurses into subterms.
Non-dependent let-bindings are converted to beta applications (via `toBetaApp`) so that
`Sym.Simp` can simplify the value and body together; dependent let-bindings are zeta-reduced.
Binders (lambdas, foralls) and irreducible forms (variables, sorts) are marked `done`
since `cbv` does not reduce under binders and there is nothing to do for variables.
-/
def cbvPreStep : Simproc := fun e => do
  match e with
  | .lit .. => foldLit e
  | .proj .. => handleProj e
  | .const .. => isOpaqueConst >> handleConst <| e
  | .app .. => simpControlCbv <|> simplifyAppFn <| e
  | .letE .. =>
    if e.letNondep! then
      let betaAppResult ← toBetaApp e
      return .step (betaAppResult.e) (betaAppResult.h)
    else
      zetaReduce e
  | .forallE .. | .lam .. | .fvar .. | .mvar .. | .bvar .. | .sort .. => return .rfl (done := true)
  | _ => return .rfl

/--
Pre-phase simproc. Skips builtin values (nat/string/int/bitvec literals) and proof terms
before dispatching to `cbvPreStep`.
-/
def cbvPre : Simproc := isBuiltinValue <|> isProofTerm <|> cbvPreStep

/--
Post-phase simproc. Tries ground evaluation of builtin operations, then
handles function applications (unfolding, beta reduction).
-/
def cbvPost : Simproc := evalGround <|> handleApp

/--
Simplify `e` using call-by-value evaluation. Unfolds reducible definitions, ensures
maximal sharing, then runs `Sym.Simp` with `cbvPre`/`cbvPost`.
-/
public def cbvEntry (e : Expr) : MetaM Result := do
  trace[Meta.Tactic.cbv] "Called cbv tactic to simplify {e}"
  let methods := {pre := cbvPre, post := cbvPost}
  let e ← Sym.unfoldReducible e
  Sym.SymM.run do
    let e ← Sym.shareCommon e
    SimpM.run' (simp e) (methods := methods)

/--
Reduce one side of an equality goal `lhs = rhs`. When `inv = false`, reduces `lhs`;
when `inv = true`, reduces `rhs`. If the reduced side becomes definitionally equal to
the other, closes the goal. Otherwise, returns a new goal with the partially reduced equality.
-/
public def cbvGoalCore (m : MVarId) (inv : Bool := false) : MetaM (Option MVarId) := do
  Sym.SymM.run do
    let methods := {pre := cbvPre, post := cbvPost}
    let m ← Sym.preprocessMVar m
    let mType ← m.getType
    let some (_, lhs, rhs) := mType.eq? | return m
    let (toReduce, toCompare) := if inv then (rhs, lhs) else (lhs, rhs)
    let result ← SimpM.run' (simp toReduce) (methods := methods)
    match result with
    | .rfl _ =>
      unless (← isDefEq toReduce toCompare) do return m
      m.refl
      return .none
    | .step e' proof _ =>
      if (← isDefEq e' toCompare) then
        if inv then
          m.assign (← mkEqSymm proof)
        else
          m.assign proof
        return .none
      else
        if inv then
          let newGoalType ← mkEq toCompare e'
          let newGoal ← mkFreshExprMVar newGoalType
          let toAssign ← mkEqTrans newGoal proof
          m.assign toAssign
          return newGoal.mvarId!
        else
          let newGoalType ← mkEq e' toCompare
          let newGoal ← mkFreshExprMVar newGoalType
          let toAssign ← mkEqTrans proof newGoal
          m.assign toAssign
          return newGoal.mvarId!

/--
Reduce both sides of an equality goal. First reduces `lhs` (forward pass), then
`rhs` (inverse pass). Returns `none` if the goal is closed, or the residual goal.
-/
public def cbvGoal (m : MVarId) : MetaM (Option MVarId) := do
  match (← cbvGoalCore m (inv := false)) with
  | .none => return .none
  | .some m' => cbvGoalCore m' (inv := true)

/--
Attempt to close a goal of the form `decide P = true` by reducing only the LHS using `cbv`.

- If the LHS reduces to `Bool.true`, the goal is closed successfully.
- If the LHS reduces to `Bool.false`, throws a user-friendly error indicating the proposition is false.
- Otherwise, throws a user-friendly error showing where the reduction got stuck.
-/
public def cbvDecideGoal (m : MVarId) : MetaM Unit := do
  Sym.SymM.run do
    let methods := {pre := cbvPre, post := cbvPost}
    let m ← Sym.preprocessMVar m
    let mType ← m.getType
    let some (_, lhs, _) := mType.eq? |
      throwError "`decide_cbv`: expected goal of the form `decide _ = true`, got: {indentExpr mType}"
    let result ← SimpM.run' (simp lhs) (methods := methods)
    let checkResult (e : Expr) (onTrue : Sym.SymM Unit) : Sym.SymM Unit := do
      if (← Sym.isBoolTrueExpr e) then
        onTrue
      else if (← Sym.isBoolFalseExpr e) then
        throwError "`decide_cbv` failed: the proposition evaluates to `false`"
      else
        throwError "`decide_cbv` failed: could not reduce the expression to a boolean value; got stuck at: {indentExpr e}"
    match result with
    | .rfl _ => checkResult lhs (m.refl)
    | .step e' proof _ => checkResult e' (m.assign proof)


end Lean.Meta.Tactic.Cbv
