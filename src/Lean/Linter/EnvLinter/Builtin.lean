/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski

Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
module

prelude
public meta import Lean.Linter.EnvLinter.Basic
public meta import Lean.MonadEnv
public meta import Lean.ReducibilityAttrs
public meta import Lean.ProjFns
public meta import Lean.Meta.InferType

open Lean Meta

namespace Lean.Linter.EnvLinter

/-- A linter for checking whether the correct declaration constructor (`def` or `theorem`)
has been used. A `def` whose type is a `Prop` should be a `theorem`, and vice versa. -/
@[builtin_env_linter] public meta def defLemma : EnvLinter where
  noErrorsFound := "All declarations correctly marked as def/lemma."
  errorsFound := "INCORRECT DEF/LEMMA:"
  test declName := do
    if (← isAutoDecl declName) || (← isImplicitReducible declName) then
      return none
    -- Projections are generated as `def`s even when they should be `theorem`s
    if ← isProjectionFn declName then return none
    let info ← getConstInfo declName
    let isThm ← match info with
      | .defnInfo .. => pure false
      | .thmInfo ..  => pure true
      | _            => return none
    match isThm, ← isProp info.type with
    | true,  false => return some "is a lemma/theorem, should be a def"
    | false, true  => return some "is a def, should be lemma/theorem"
    | _,     _     => return none

end Lean.Linter.EnvLinter
