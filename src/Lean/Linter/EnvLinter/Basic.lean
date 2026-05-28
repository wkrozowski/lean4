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
public import Lean.Structure
public import Lean.Elab.InfoTree.Main
public import Lean.AutoDecl
public import Lean.Linter.EnvLinter.Snapshot
public import Lean.Attributes
import Lean.ExtraModUses

public section

open Lean Meta

namespace Lean.Linter.EnvLinter

/-!
# Environment linter framework

An environment linter is a check on a single declaration, designed for `lake builtin-lint`
to inspect the whole environment post-build. Each env linter is associated with a
`Lean.Option Bool`:

```
register_builtin_option linter.X : Bool := { defValue := true, descr := "..." }
initialize Lean.Linter.addEnvLinterOption linter.X

@[builtin_env_linter linter.X]
public meta def myLinter : EnvLinter where
  test := fun declName => ...
  noErrorsFound := "..."
  errorsFound := "..."
```

`addEnvLinterOption linter.X` (in an `initialize` block) records the option in
`envLinterOptionsRef`, so that `Lean.addDecl` will snapshot its resolved value for each
non-auto declaration in any downstream module that imports this one. The
`@[builtin_env_linter linter.X]` attribute records the linter in `envLinterExt` at elab time
(so it persists in the olean for `lake builtin-lint` to consume).

To opt a single declaration out of a particular linter, use
`set_option linter.X false in <decl>`. The setting is captured by the snapshot.

**Module-system note:** downstream modules that want env linters from a module-system
library must import it with `meta` qualification — e.g., `public meta import MyLintersLib`.
A plain `public import` does not fire the library's `initialize addEnvLinterOption` blocks,
so the snapshot is built with an empty options registry and the linter never sees any
declarations. This matches how `meta`-imports run initializers as part of metaprogram
execution at elab time.
-/

/-- An environment linting test for the `lake builtin-lint` command. -/
structure EnvLinter where
  /-- `test` defines a test to perform on every declaration. It should never fail. Returning `none`
  signifies a passing test. Returning `some msg` reports a failing test with error `msg`. -/
  test : Name → MetaM (Option MessageData)
  /-- `noErrorsFound` is the message printed when all tests are negative -/
  noErrorsFound : MessageData
  /-- `errorsFound` is printed when at least one test is positive -/
  errorsFound : MessageData

/-- An `EnvLinter` paired with the option that controls it and the underlying declaration
name. Identity is the option name; that is what appears in CLI flags, diagnostic headers,
and `set_option`. -/
structure NamedEnvLinter extends EnvLinter where
  /-- The name of the `Lean.Option Bool` that controls the linter; also the linter's
  user-facing identifier. -/
  optName : Name
  /-- The full declaration name of the linter (used to look up its `test` function). -/
  declName : Name

/-- Resolves a registered environment linter into a `NamedEnvLinter` by evaluating the linter's
declaration. -/
def getEnvLinter (optName declName : Name) : CoreM NamedEnvLinter := unsafe do
  let linter ← evalConstCheck EnvLinter ``EnvLinter declName
  return { linter with optName, declName }

/--
Defines the `@[builtin_env_linter linter.X]` attribute for registering an environment linter.

The argument names the controlling `Lean.Option Bool`, which must be a declared constant of
type `Lean.Option Bool`. (Typically declared via `register_builtin_option` or `register_option`
together with `initialize addEnvLinterOption linter.X`.) Each option may be the target of at
most one linter (the option is the linter's identity).
-/
syntax (name := builtin_env_linter) "builtin_env_linter " ident : attr

builtin_initialize registerBuiltinAttribute {
  name := `builtin_env_linter
  descr := "Use this declaration as a linting test in `lake builtin-lint`"
  add   := fun decl stx kind => do
    unless kind == .global do throwError "invalid attribute `builtin_env_linter`, must be global"
    let optName ← match stx with
      | `(attr| builtin_env_linter $id:ident) => pure id.getId
      | _ => throwError "invalid `builtin_env_linter` syntax: expected an option name argument"
    let env ← getEnv
    unless env.contains optName do
      throwError "invalid attribute `builtin_env_linter`, no constant named `{optName}`; \
        did you forget `register_builtin_option {optName} : Bool := ...`?"
    if let some declName := (envLinterExt.getState env).find? optName then
      Elab.addConstInfo stx declName
      throwError
        "invalid attribute `builtin_env_linter`, option `{optName}` is already controlling \
        linter `{declName}`"
    let isNotPrivate := !isPrivateName decl; let isMeta := isMarkedMeta env decl
    unless isNotPrivate && isMeta do
      throwError "invalid attribute `builtin_env_linter`, declaration \
        `{.ofConstName decl}` must be marked as `meta` and must not be `private` (and must be \
        `public` under the module system).\n\
        Currently {if isNotPrivate then "non-private" else "private"} and \
        {if isMeta then "meta" else "non-meta"}."
    let constInfo ← getConstInfo decl
    unless ← (isDefEq constInfo.type (mkConst ``EnvLinter)).run' do
      throwError "`{.ofConstName decl}` must have type `{.ofConstName ``EnvLinter}`, got \
        `{constInfo.type}`"
    modifyEnv fun env => envLinterExt.addEntry env (optName, decl)
}

end Lean.Linter.EnvLinter
