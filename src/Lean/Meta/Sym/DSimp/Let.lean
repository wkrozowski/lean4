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
Definitionally simplifies a `let`/`have` expression.

No `toBetaApp`/`simpBetaApp`/`toHave` round-trip (that exists in `Sym.Simp` only to keep
proofs linear). To be implemented (see `dsimp.md`).
-/
public def dsimpLet : DSimproc := fun _ => return .rfl

end Lean.Meta.Sym.DSimp
