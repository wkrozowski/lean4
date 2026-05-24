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
Definitionally simplifies a forall expression.

Unlike `Sym.Simp.simpForall`, this should descend into the binder type as well as the
body. No `dsimpArrow` special case — `→` is handled uniformly with `∀`. To be implemented
(see `dsimp.md`).
-/
public def dsimpForall : DSimproc := fun _ => return .rfl

end Lean.Meta.Sym.DSimp
