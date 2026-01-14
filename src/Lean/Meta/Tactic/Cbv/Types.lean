/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Rozowski
-/
module

prelude
public import Lean.Expr
public section

namespace Lean.Meta.Cbv

structure Result where
  value : Expr
  proof : Expr
  isValue : Int


end Lean.Meta.Cbv
