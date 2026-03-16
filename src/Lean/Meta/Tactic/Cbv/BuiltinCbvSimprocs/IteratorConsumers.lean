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
public import Init.Data.Iterators.Consumers.Loop

namespace Lean.Meta.Tactic.Cbv

/-- Rewrite `Iter.fold f init it` to `it.toList.foldl f init`.

This uses `Iter.foldl_toList` (reversed) to bypass the `ForIn.forIn` chain,
which contains dependent types that cbv's congruence-based rewriting cannot handle.
After this rewrite, cbv can evaluate `it.toList` via the extrinsic fix simprocs
and then evaluate `List.foldl` natively. -/
builtin_cbv_simproc cbv_eval simpIterFold (Std.Iter.fold _ _ _) := fun e => do
  -- e = @Std.Iter.fold.{w, x} α β γ instIter instLoop f init it
  let args := e.getAppArgs
  if args.size < 8 then return .rfl
  let α := args[0]!
  let β := args[1]!
  let γ := args[2]!
  let instIter := args[3]!
  let instLoop := args[4]!
  let f := args[5]!
  let init := args[6]!
  let it := args[7]!
  try
    -- Build @Std.Iter.foldl_toList α β γ instIter _ instLoop _ f init it
    -- where _ positions (Finite α Id, LawfulIteratorLoop α Id Id) are synthesized.
    -- Result type: it.toList.foldl f init = it.fold f init
    let foldlToList ← Meta.mkAppOptM `Std.Iter.foldl_toList
      #[some α, some β, some γ, some instIter, none, some instLoop, none, some f, some init, some it]
    -- Reverse: it.fold f init = it.toList.foldl f init
    let proof ← Meta.mkAppM ``Eq.symm #[foldlToList]
    let proofType ← Meta.inferType proof
    let some (_, _, rhs) := proofType.eq? | return .rfl
    let rhs ← Sym.share rhs
    return .step rhs proof
  catch _ =>
    return .rfl

/-- Rewrite `Iter.any p it` to `it.toList.any p`.

Uses `Iter.any_toList` (reversed) to bypass `ForIn.forIn`. -/
builtin_cbv_simproc cbv_eval simpIterAny (Std.Iter.any _ _) := fun e => do
  -- e = @Std.Iter.any.{w} α β instIter instLoop p it
  let args := e.getAppArgs
  if args.size < 6 then return .rfl
  let α := args[0]!
  let β := args[1]!
  let instIter := args[2]!
  let instLoop := args[3]!
  let p := args[4]!
  let it := args[5]!
  try
    -- @Std.Iter.any_toList α β instIter _ instLoop _ it p
    -- where _ are Finite α Id and LawfulIteratorLoop α Id Id
    -- Result type: it.toList.any p = it.any p
    let anyToList ← Meta.mkAppOptM `Std.Iter.any_toList
      #[some α, some β, some instIter, none, some instLoop, none, some it, some p]
    let proof ← Meta.mkAppM ``Eq.symm #[anyToList]
    let proofType ← Meta.inferType proof
    let some (_, _, rhs) := proofType.eq? | return .rfl
    let rhs ← Sym.share rhs
    return .step rhs proof
  catch _ =>
    return .rfl

/-- Rewrite `Iter.all p it` to `it.toList.all p`.

Uses `Iter.all_toList` (reversed) to bypass `ForIn.forIn`. -/
builtin_cbv_simproc cbv_eval simpIterAll (Std.Iter.all _ _) := fun e => do
  -- e = @Std.Iter.all.{w} α β instIter instLoop p it
  let args := e.getAppArgs
  if args.size < 6 then return .rfl
  let α := args[0]!
  let β := args[1]!
  let instIter := args[2]!
  let instLoop := args[3]!
  let p := args[4]!
  let it := args[5]!
  try
    -- @Std.Iter.all_toList α β instIter _ instLoop _ it p
    let allToList ← Meta.mkAppOptM `Std.Iter.all_toList
      #[some α, some β, some instIter, none, some instLoop, none, some it, some p]
    let proof ← Meta.mkAppM ``Eq.symm #[allToList]
    let proofType ← Meta.inferType proof
    let some (_, _, rhs) := proofType.eq? | return .rfl
    let rhs ← Sym.share rhs
    return .step rhs proof
  catch _ =>
    return .rfl

end Lean.Meta.Tactic.Cbv
