/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude

public import Lean.Elab.Tactic.Conv.Basic
public import Lean.Meta.Tactic.Cbv
public section

namespace Lean.Elab.Tactic.Conv
open Meta

@[builtin_tactic Lean.Parser.Tactic.Conv.cbv] def evalCbv : Tactic := fun _ => withMainContext do
  let lhs ← getLhs
  trace[Meta.Tactic] "[conv.cbv]: lhs is {lhs}"
  let ⟨rhs, heq⟩ ← Meta.cbv lhs
  updateLhs rhs heq


end Lean.Elab.Tactic.Conv
