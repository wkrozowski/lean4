/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.DSimp.DSimpM
namespace Lean.Meta.Sym.DSimp

/--
Definitionally simplifies a lambda expression.

Unlike `Sym.Simp.simpLambda`, this should descend into the binder type as well as the
body. To be implemented (see `dsimp.md`).
-/
public def dsimpLambda : DSimproc := fun _ => return .rfl

end Lean.Meta.Sym.DSimp
