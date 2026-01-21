/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Rozowski
-/
module

prelude
public import Lean.Expr
public import Lean.Meta.Basic
public import Std.Data.HashMap
public import Lean.Meta.CongrTheorems
public import Lean.Meta.DiscrTree
public section

namespace Lean.Meta.Tactic.Cbv

structure Result where
  value : Expr
  proof : Expr
  isValue : Bool

structure Key where
  functionType : Expr
  arity : Nat
deriving BEq, Hashable

structure CbvState where
  compositionThms : Std.HashMap Key CongrTheorem
  leftCongruenceThms : Std.HashMap Key Expr
  fullyEvaluated : Std.HashSet Expr

abbrev CbvM := StateT CbvState MetaM

abbrev CbvProc := (e : Expr) → (callback : Expr → CbvM Result) → CbvM (Option Result)

structure ExtensionState where
  tree : DiscrTree CbvProc := {}
  deriving Inhabited

structure CbvExt where
  /-- Attempts to prove an expression is equal to some explicit vale the relevant type. -/
  eval : CbvProc
  /-- The name of the `cbv` extension. -/
  name : Name := by exact decl_name%

/-- The state of the `cbv` extension environment -/
structure CbvExtState where
  /-- The tree of `cbv` extensions. -/
  tree : DiscrTree CbvExt := {}
  deriving Inhabited

inductive CbvCongrArgKind where
  -- Requires the proof that it evaluates to a value
  | eval
  -- It is a value, no need to pass the proof
  | value
  -- Needs to be finished off with refl
  | refl
  deriving Inhabited, Repr, BEq

instance : ToMessageData CbvCongrArgKind where
  toMessageData := fun a => match a with
  | .eval => "eval"
  | .refl => "refl"
  | .value => "value"

abbrev Entry := Array (Array DiscrTree.Key) × Name

end Lean.Meta.Tactic.Cbv
