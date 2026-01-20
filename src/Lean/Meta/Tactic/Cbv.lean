/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Cbv.Types
public import Lean.Meta.Tactic.Cbv.Main

public section

namespace Lean

builtin_initialize registerTraceClass `Meta.Tactic.cbv
builtin_initialize registerTraceClass `Meta.Tactic.cbv.congr (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.cbv.value (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.cbv.unfold (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.cbv.matcher (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.cbv.recursor (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.cbv.projection (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.cbv.app (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.cbv.irreducible (inherited := true)
builtin_initialize registerTraceClass `Debug.Meta.Tactic.cbv
builtin_initialize registerTraceClass `Debug.Meta.Tactic.cbv.congr (inherited := true)

end Lean
