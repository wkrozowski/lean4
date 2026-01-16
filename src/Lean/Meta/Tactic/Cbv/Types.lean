/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Rozowski
-/
module

prelude
public import Lean.Expr
public import Lean.Meta.Basic
public section

namespace Lean.Meta.Tactic.Cbv

structure Result where
  value : Expr
  proof : Expr
  isValue : Bool

abbrev CbvM := MetaM

end Lean.Meta.Tactic.Cbv
