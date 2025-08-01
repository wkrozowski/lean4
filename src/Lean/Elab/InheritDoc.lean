/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

prelude
public import Lean.Elab.InfoTree.Main
public import Lean.DocString.Extension

public section

namespace Lean

/--
Uses documentation from a specified declaration.

`@[inherit_doc decl]` is used to inherit the documentation from the declaration `decl`.
-/
@[builtin_doc]
builtin_initialize
  registerBuiltinAttribute {
    name := `inherit_doc
    descr := "inherit documentation from a specified declaration"
    add   := fun decl stx kind => do
      unless kind == AttributeKind.global do
        throwAttrMustBeGlobal `inherit_doc kind
      match stx with
      | `(attr| inherit_doc $[$id?:ident]?) => withRef stx[0] do
        let some id := id?
          | throwError "Invalid `[inherit_doc]` attribute: Could not infer doc source"
        let declName ← Elab.realizeGlobalConstNoOverloadWithInfo id
        if (← findSimpleDocString? (← getEnv) decl (includeBuiltin := false)).isSome then
          logWarning m!"{← mkConstWithLevelParams decl} already has a doc string"
        let some doc ← findSimpleDocString? (← getEnv) declName
          | logWarningAt id m!"{← mkConstWithLevelParams declName} does not have a doc string"
        -- This docstring comes from the environment, so documentation links have already been validated
        addDocStringCore decl doc
      | _  => throwError "Invalid `[inherit_doc]` attribute syntax"
  }
