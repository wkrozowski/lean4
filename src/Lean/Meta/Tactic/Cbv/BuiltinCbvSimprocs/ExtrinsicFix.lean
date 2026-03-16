/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.InferType
import Init.CbvSimproc
import Lean.Meta.Tactic.Cbv.CbvSimproc
import Lean.Meta.AppBuilder
import Lean.Meta.SynthInstance
import Lean.Meta.WHNF
import Init.WFExtrinsicFix
public import Init.Data.Iterators.Basic
public import Init.Data.Iterators.Consumers.Monadic.Loop

namespace Lean.Meta.Tactic.Cbv

/-- Reduce `Shrink.inflate (Shrink.deflate x)` to `x`
using the theorem `Shrink.inflate_deflate`.
If the argument is not literally `Shrink.deflate x`, try whnf reduction first
(e.g. to see through `liftM` in monadic iterator combinators). -/
builtin_cbv_simproc cbv_eval simpShrinkInflate (Std.Shrink.inflate _) := fun e => do
  let arg := e.appArg!
  let arg' ← match_expr arg with
    | Std.Shrink.deflate _ _ => pure arg
    | _ => Meta.whnf arg
  match_expr arg' with
  | Std.Shrink.deflate α x =>
    let result ← Sym.share x
    let levels := e.getAppFn.constLevels!
    let proof := mkApp2 (mkConst ``Std.Shrink.inflate_deflate levels) α x
    return .step result proof
  | _ => return .rfl

/--
Try to prove `WellFounded R` for a relation `R`.

Handles:
- `InvImage r f`: recursively proves `WellFounded r`, then applies `InvImage.wf`
- `IteratorLoop.rel α m P`: proves via `wellFounded_of_finite` if `[Finite α m]`
- Relations with a `WellFoundedRelation` instance on the domain type
-/
private partial def proveWellFounded? (R : Expr) : MetaM (Option Expr) := do
  -- Case 1: R is `InvImage r f`
  match_expr R with
  | InvImage _α _β r f =>
    let some wfR ← proveWellFounded? r | return none
    try
      return some (← Meta.mkAppM ``InvImage.wf #[f, wfR])
    catch _ =>
      return none
  | _ => pure ()
  -- Case 2: R is `IteratorLoop.rel α m P` — prove via `wellFounded_of_finite`
  if R.getAppNumArgs ≥ 6 then
    let fn := R.getAppFn
    if fn.isConst && fn.constName! == ``Std.IteratorLoop.rel then
      let rArgs := R.getAppArgs
      -- IteratorLoop.rel.{w, w', x} α m β inst γ P
      let α := rArgs[0]!
      let m := rArgs[1]!
      let β := rArgs[2]!
      let iterInst := rArgs[3]!
      let γ := rArgs[4]!
      let P := rArgs[5]!
      try
        -- Synthesize Finite α m
        let finiteType ← Meta.mkAppM ``Std.Iterators.Finite #[α, m]
        let some finiteInst ← Meta.synthInstance? finiteType | return none
        let levels := fn.constLevels!
        -- wellFounded_of_finite.{w, w', x} : @WellFounded ... (IteratorLoop.rel ...)
        let proof := mkAppN (mkConst ``Std.IteratorLoop.wellFounded_of_finite levels)
          #[m, α, β, γ, iterInst, finiteInst, P]
        return some proof
      catch e =>
        trace[Meta.Tactic.cbv] "proveWellFounded? IteratorLoop.rel failed: {e.toMessageData}"
        return none
  -- Case 3: Try to find WellFoundedRelation instance for the domain type
  let rType ← Meta.inferType R
  let some (domType, _) := rType.arrow? | return none
  try
    let u ← Meta.getLevel domType
    let wfrType := mkApp (mkConst ``WellFoundedRelation [u]) domType
    let some wfrInst ← Meta.synthInstance? wfrType | return none
    let instRel := mkApp2 (mkConst ``WellFoundedRelation.rel [u]) domType wfrInst
    if (← Meta.isDefEq instRel R) then
      return some (mkApp2 (mkConst ``WellFoundedRelation.wf [u]) domType wfrInst)
    else
      return none
  catch _ =>
    return none

/-- Unfold `extrinsicFix₂ R F a b` one step using `extrinsicFix₂_eq_apply`. -/
builtin_cbv_simproc cbv_eval simpExtrinsicFix₂ (WellFounded.extrinsicFix₂ _ _ _ _) := fun e => do
  let args := e.getAppArgs
  if args.size < 8 then return .rfl
  let R := args[4]!
  let some wfProof ← proveWellFounded? R | return .rfl
  let levels := e.getAppFn.constLevels!
  let proof := mkAppN (mkConst ``WellFounded.extrinsicFix₂_eq_apply levels)
    #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!, wfProof, args[6]!, args[7]!]
  let proofType ← Meta.inferType proof
  let some (_, _, rhs) := proofType.eq? | return .rfl
  let rhs ← Sym.share rhs
  return .step rhs proof

/-- Unfold `extrinsicFix R F a` one step using `extrinsicFix_eq_apply`. -/
builtin_cbv_simproc cbv_eval simpExtrinsicFix (WellFounded.extrinsicFix _ _ _) := fun e => do
  let args := e.getAppArgs
  if args.size < 6 then return .rfl
  let R := args[3]!
  let some wfProof ← proveWellFounded? R | return .rfl
  let levels := e.getAppFn.constLevels!
  let proof := mkAppN (mkConst ``WellFounded.extrinsicFix_eq_apply levels)
    #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, wfProof, args[5]!]
  let proofType ← Meta.inferType proof
  let some (_, _, rhs) := proofType.eq? | return .rfl
  let rhs ← Sym.share rhs
  return .step rhs proof

/-- Unfold `extrinsicFix₃ R F a b c` one step using `extrinsicFix₃_eq_apply`. -/
builtin_cbv_simproc cbv_eval simpExtrinsicFix₃ (WellFounded.extrinsicFix₃ _ _ _ _ _) := fun e => do
  let args := e.getAppArgs
  if args.size < 10 then return .rfl
  let R := args[5]!
  let some wfProof ← proveWellFounded? R | return .rfl
  let levels := e.getAppFn.constLevels!
  let proof := mkAppN (mkConst ``WellFounded.extrinsicFix₃_eq_apply levels)
    #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!, args[6]!, wfProof, args[7]!, args[8]!, args[9]!]
  let proofType ← Meta.inferType proof
  let some (_, _, rhs) := proofType.eq? | return .rfl
  let rhs ← Sym.share rhs
  return .step rhs proof

end Lean.Meta.Tactic.Cbv
