/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Basic
import Lean.Linter.Init
import Lean.Elab.InfoTree.Main
import Lean.ExtraModUses
import Init.Omega

public section

namespace Lean.Linter

register_builtin_option linter.deprecated : Bool := {
  defValue := true
  descr := "if true, generate deprecation warnings"
}

register_builtin_option linter.deprecated.transitiveFuel : Nat := {
  defValue := 100
  descr := "maximum number of steps to follow when checking whether a `@[deprecated]` attribute \
    points at a declaration that is itself deprecated; set to 0 to disable that check"
}

structure DeprecationEntry where
  newName? : Option Name := none
  text? : Option String := none
  since? : Option String := none
  deriving Inhabited

/-- Outcome of following a chain of `@[deprecated]` redirections. See `followDeprecation`. -/
inductive TransitiveDeprecation where
  /-- The chain ends at `finalName`, which is not itself deprecated. -/
  | replacement (finalName : Name)
  /-- The chain ends at `lastName`, which is deprecated without an explicit replacement. -/
  | noReplacement (lastName : Name)
  /-- The chain is longer than the allotted fuel. -/
  | exhausted

/--
Follows the chain of deprecations starting at `name`, using at most `fuel` steps: as long as the
current declaration is deprecated in favor of another declaration, moves on to that declaration.
`getEntry` looks up the `DeprecationEntry` (if any) for a declaration.
-/
def followDeprecation (getEntry : Name → Option DeprecationEntry) :
    Nat → Name → TransitiveDeprecation
  | 0, _ => .exhausted
  | fuel + 1, name =>
    match getEntry name with
    | none       => .replacement name
    | some entry =>
      match entry.newName? with
      | none      => .noReplacement name
      -- guard against a declaration deprecated in favor of itself
      | some next => if next == name then .noReplacement name
                     else followDeprecation getEntry fuel next

open Meta in
/--
If the initial declaration `oldName` and its suggested replacement `newName` have different types
(up to reducible defeq), returns an explanatory note. Used to flag that a transitive replacement may
not be a drop-in substitute.
-/
def deprecationTypeMismatchNote? (oldName newName : Name) : CoreM (Option MessageData) := do
  let env ← getEnv
  let some old := env.find? oldName | return none
  let some new := env.find? newName | return none
  if ← MetaM.run' <| withReducible <| isDefEqGuarded old.type new.type then
    return none
  return some <| .note m!"The suggested replacement has a different type:{indentExpr new.type}\
    \ninstead of{indentExpr old.type}"

builtin_initialize deprecatedAttr : ParametricAttribute DeprecationEntry ← do
  let ext ← registerParametricAttributeExt (α := DeprecationEntry) `deprecated
  registerParametricAttributeForExt (ext := ext) {
    name := `deprecated
    descr := "mark declaration as deprecated",
    getParam := fun declName stx => do
      let `(attr| deprecated $[$id?]? $[$text?]? $[(since := $since?)]?) := stx
        | throwError "Invalid `[deprecated]` attribute syntax"
      let newName? ← id?.mapM Elab.realizeGlobalConstNoOverloadWithInfo
      if let some newName := newName? then
        recordExtraModUseFromDecl (isMeta := false) newName
        -- Warn if `newName` is itself deprecated, so the deprecation points at the ultimate target.
        let fuel := linter.deprecated.transitiveFuel.get (← getOptions)
        if fuel > 0 && getLinterValue linter.deprecated (← getLinterOptions) then
          let env ← getEnv
          let getEntry n := ParametricAttribute.getParamFromExt? ext (preserveOrder := false) env n
          match followDeprecation getEntry fuel newName with
          | .replacement finalName =>
            if finalName != newName && finalName != declName then
              let mut msg := m!"`{.ofConstName newName true}` is itself deprecated in favor of \
                `{.ofConstName finalName true}`; consider deprecating `{.ofConstName declName true}` \
                in favor of `{.ofConstName finalName true}` instead"
              if let some note ← deprecationTypeMismatchNote? declName finalName then
                msg := msg ++ note
              logWarning msg
          | .noReplacement lastName =>
            let via := if lastName == newName then m!""
              else m!" (via a chain of deprecations ending at `{.ofConstName lastName true}`)"
            logWarning m!"`{.ofConstName newName true}` is itself deprecated{via}, but without an \
              explicit replacement; `{.ofConstName declName true}` is being deprecated in favor of \
              a deprecated declaration"
          | .exhausted =>
            logWarning m!"the deprecation chain starting at `{.ofConstName newName true}` exceeds \
              {fuel} steps; consider deprecating `{.ofConstName declName true}` in favor of a \
              non-deprecated declaration"
      let text? := text?.map TSyntax.getString
      let since? := since?.map TSyntax.getString
      if id?.isNone && text?.isNone then
        logWarning "`[deprecated]` attribute should specify either a new name or a deprecation message"
      if since?.isNone then
        logWarning "`[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := \"...\")`"
      return { newName?, text?, since? }
  }

def setDeprecated {m} [Monad m] [MonadEnv m] [MonadError m] (declName : Name) (entry : DeprecationEntry) : m Unit := do
  let env ← getEnv
  match deprecatedAttr.setParam env declName entry with
  | Except.ok env   => setEnv env
  | Except.error ex => throwError ex

def isDeprecated (env : Environment) (declName : Name) : Bool :=
  Option.isSome <| deprecatedAttr.getParam? env declName

def _root_.Lean.MessageData.isDeprecationWarning (msg : MessageData) : Bool :=
  msg.hasTag (· == ``deprecatedAttr)

def getDeprecatedNewName (env : Environment) (declName : Name) : Option Name := do
  (← deprecatedAttr.getParam? env declName).newName?

open Meta in
def checkDeprecated (declName : Name) : MetaM Unit := do
  if getLinterValue linter.deprecated (← getLinterOptions) then
    let some attr := deprecatedAttr.getParam? (← getEnv) declName | pure ()
    let extraMsg ← match attr.text?, attr.newName? with
      | some text, _ => pure m!": {text}"
      | none, none => pure m!""
      | none, some newName => do
        let mut msg := m!": Use `{.ofConstName newName true}` instead"
        let env ← getEnv
        let oldPfx := declName.getPrefix
        let newPfx := newName.getPrefix
        let some oldDecl := env.find? declName | pure msg
        let some newDecl := env.find? newName | pure msg
        if !(← withReducible <| isDefEqGuarded oldDecl.type newDecl.type) then
          msg := msg ++ .note m!"The updated constant has a different type:{indentExpr newDecl.type}\
            \ninstead of{indentExpr oldDecl.type}"
        unless oldPfx.isAnonymous do
          -- Check namespace, then visibility, exclusively and in this order, to avoid redundancy
          if oldPfx != newPfx then
            let changeEx := if let .str _ oldRoot := declName then
              m!" (e.g., from `x.{oldRoot}` to `{.ofConstName newName} x`)"
            else .nil
            msg := msg ++ .note m!"The updated constant is in a different namespace. \
              Dot notation may need to be changed{changeEx}."
          else if !(isProtected env declName) && isProtected env newName then
            let pfxComps := newPfx.componentsRev
            let pfxCompStr := if _ : pfxComps.length > 1 then m!"at least the last component `{pfxComps[0]}` of " else ""
            msg := msg ++ .note m!"`{.ofConstName newName true}` is protected. References to this \
              constant must include {pfxCompStr}its prefix `{newPfx}` even when inside its namespace."
        pure msg
    logWarning <| .tagged ``deprecatedAttr <|
      m!"`{.ofConstName declName true}` has been deprecated" ++ extraMsg
