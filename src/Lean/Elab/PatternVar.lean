/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Match.MatchPatternAttr
public import Lean.Meta.Hint
public import Lean.Elab.Arg
public import Lean.Elab.MatchAltView

public section

namespace Lean.Elab.Term

open Meta

abbrev PatternVar := Syntax  -- TODO: should be `Ident`

/-!
  Patterns define new local variables.
  This module collects them and preprocesses `_` occurring in patterns.
  Recall that an `_` may represent anonymous variables or inaccessible terms
  that are implied by typing constraints. Thus, we represent them with fresh named holes `?x`.
  After we elaborate the pattern, if the metavariable remains unassigned, we transform it into
  a regular pattern variable. Otherwise, it becomes an inaccessible term.

  Macros occurring in patterns are expanded before the `collectPatternVars` method is executed.
  The following kinds of Syntax are handled by this module
  - Constructor applications
  - Applications of functions tagged with the `[match_pattern]` attribute
  - Identifiers
  - Anonymous constructors
  - Structure instances
  - Inaccessible terms
  - Named patterns
  - Tuple literals
  - Type ascriptions
  - Literals: num, string and char
-/
namespace CollectPatternVars

/-- State for the pattern variable collector monad. -/
structure State where
  /-- Pattern variables found so far. -/
  found     : NameSet := {}
  /-- Pattern variables found so far as an array. It contains the order they were found. -/
  vars      : Array PatternVar := #[]
  deriving Inhabited

abbrev M := StateRefT State TermElabM

private def throwCtorExpected {α} (ident : Option Syntax) : M α := do
  let message : MessageData :=
    "Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`"
  let some idStx := ident | throwError message
  let name := idStx.getId
  if let .anonymous := name then throwError message
  let env ← getEnv
  let mut candidates : Array Name := #[]
  for (c, _) in env.constants do
    if isPrivateName c then continue
    if !(name.isSuffixOf c) then continue
    if env.isConstructor c || hasMatchPatternAttribute env c then
      candidates := candidates.push c

  if candidates.size = 0 then
    throwError message
  else if h : candidates.size = 1 then
    throwError message ++ .hint' m!"'{candidates[0]}' is similar"
  else
    let sorted := candidates.qsort (·.toString < ·.toString)
    let diff :=
      if candidates.size > 10 then [m!" (or {candidates.size - 10} others)"]
      else []
    let suggestions : MessageData := .group <|
      .joinSep ((sorted.extract 0 10 |>.toList |>.map (showName env)) ++ diff)
        ("," ++ Format.line)
    throwError message ++ .group (.hint' ("These are similar:" ++ .nestD (Format.line ++ suggestions)))
where
  -- Create some `MessageData` for a name that shows it without an `@`, but with the metadata that
  -- makes infoview hovers and the like work. This technique only works because the names are known
  -- to be global constants, so we don't need the local context.
  showName (env : Environment) (n : Name) : MessageData :=
    let params :=
      env.constants.find?' n |>.map (·.levelParams.map Level.param) |>.getD []
    .ofFormatWithInfos {
      fmt := "'" ++ .tag 0 (format n) ++ "'",
      infos :=
        .ofList [(0, .ofTermInfo {
          lctx := .empty,
          expr := .const n params,
          stx := .ident .none (toString n).toSubstring n [.decl n []],
          elaborator := `Delab,
          expectedType? := none
        })] _
    }

private def throwInvalidPattern {α} : M α :=
  throwError "Invalid pattern"

/-!
An application in a pattern can be

1- A constructor application
   The elaborator assumes fields are accessible and inductive parameters are not accessible.

2- A regular application `(f ...)` where `f` is tagged with `[match_pattern]`.
   The elaborator assumes implicit arguments are not accessible and explicit ones are accessible.
-/

structure Context where
  funId         : Ident
  ctorVal?      : Option ConstructorVal -- It is `some`, if constructor application
  explicit      : Bool
  ellipsis      : Bool
  paramDecls    : Array (Name × BinderInfo) -- parameters' names and binder information
  paramDeclIdx  : Nat := 0
  namedArgs     : Array NamedArg
  usedNames     : Std.HashSet Name := {}
  args          : List Arg
  newArgs       : Array Term := #[]
  deriving Inhabited

private def throwInvalidNamedArgs (ctx : Context) (h : !ctx.namedArgs.isEmpty) : MetaM α := do
  let names := (ctx.namedArgs.map fun narg => m!"`{narg.name}`").toList
  let nameStr := if names.length == 1 then "name" else "names"
  let validNames := ctx.paramDecls.filterMap fun (name, _) =>
    if name.hasMacroScopes then none else some name
  have h := Nat.zero_lt_of_ne_zero (mt Array.isEmpty_iff_size_eq_zero.mpr (Bool.not_eq.mp h))
  -- We offer hints only for the first argument
  let firstNamedArg := ctx.namedArgs[0]'h
  let replacementSpan := firstNamedArg.ref[1]
  let unused := validNames.filter (!ctx.usedNames.contains ·)
  let hint ← do
    if replacementSpan.getHeadInfo matches .original .. then
      let suggestions := unused.map fun validName =>
        { suggestion := validName.toString
          span? := replacementSpan
          preInfo? := some s!"`{validName}`: "
          toCodeActionTitle? := some fun s => s!"Change argument name `{firstNamedArg.name}` to `{s}`" }
      let hintMsg := m!"Replace `{firstNamedArg.name}` with one of the following parameter names:"
      MessageData.hint (forceList := true) hintMsg suggestions
    else
      let validNamesMsg := MessageData.orList <| unused.map (m!"`{·}`") |>.toList
      pure <| MessageData.hint' m!"Perhaps you meant one of the following parameter names: {validNamesMsg}"
  throwError m!"Invalid argument {nameStr} {.andList names} for function `{ctx.funId}`" ++ hint

private def isDone (ctx : Context) : Bool :=
  ctx.paramDeclIdx ≥ ctx.paramDecls.size

private def getNextParam (ctx : Context) : (Name × BinderInfo) × Context :=
  let i := ctx.paramDeclIdx
  let d := ctx.paramDecls[i]!
  (d, { ctx with paramDeclIdx := ctx.paramDeclIdx + 1 })

private def throwWrongArgCount (ctx : Context) (tooMany : Bool) : M α := do
  let numExpectedArgs :=
    (if ctx.explicit then ctx.paramDecls else ctx.paramDecls.filter (·.2.isExplicit)).size
  -- If we have too few arguments because we skipped invalid named args, show that error instead
  if !tooMany && !ctx.namedArgs.isEmpty then checkNamedArgs
  let argKind := if ctx.explicit then "" else "explicit "
  let argWord := if numExpectedArgs == 1 then "argument" else "arguments"
  let discrepancyKind := if tooMany then "Too many" else "Not enough"
  let mut msg := m!"Invalid pattern: {discrepancyKind} arguments to '{ctx.funId}'; \
    expected {numExpectedArgs} {argKind}{argWord}"
  if !tooMany then
    msg := msg ++ .hint' "To ignore all remaining arguments, use the ellipsis notation `..`"
  throwError msg
where
  checkNamedArgs := do
    let mut ctx := ctx
    let mut remainingNames : Std.HashSet Name := {}
    -- If there were too few (unnamed) arguments, we may not have processed the parameters that
    -- match the outstanding named arguments, so some names in `namedArgs` may be valid
    while !isDone ctx do
      let ((name, _), ctx') := getNextParam ctx
      ctx := ctx'
      if let some idx := ctx'.namedArgs.findFinIdx? fun namedArg => namedArg.name == name then
        ctx := { ctx with namedArgs := ctx.namedArgs.eraseIdx idx
                          usedNames := ctx.usedNames.insert name }
    if h : !ctx.namedArgs.isEmpty then
      throwInvalidNamedArgs ctx h

private def finalize (ctx : Context) : M Syntax := do
  if ctx.args.isEmpty then
    if h : !ctx.namedArgs.isEmpty then
      throwInvalidNamedArgs ctx h
    else
      let fStx ← `(@$(ctx.funId):ident)
      return Syntax.mkApp fStx ctx.newArgs
  else
    throwWrongArgCount ctx true

private def isNextArgAccessible (ctx : Context) : Bool :=
  let i := ctx.paramDeclIdx
  match ctx.ctorVal? with
  | some ctorVal => i ≥ ctorVal.numParams -- For constructor applications only fields are accessible
  | none =>
    if h : i < ctx.paramDecls.size then
      -- For `[match_pattern]` applications, only explicit parameters are accessible.
      let d := ctx.paramDecls[i]
      d.2.isExplicit
    else
      false

private def processVar (idStx : Syntax) : M Syntax := do
  unless idStx.isIdent do
    throwErrorAt idStx "Invalid pattern variable: Identifier expected, but found{indentD idStx}"
  let id := idStx.getId
  unless id.eraseMacroScopes.isAtomic do
    throwError "Invalid pattern variable: Variable name must be atomic, but '{id}' has multiple components"
  if (← get).found.contains id then
    throwError "Invalid pattern variable: Variable name '{id}' was already used"
  modify fun s => { s with vars := s.vars.push idStx, found := s.found.insert id }
  return idStx

private def samePatternsVariables (startingAt : Nat) (s₁ s₂ : State) : Bool := Id.run do
  if h₁ : s₁.vars.size = s₂.vars.size then
    for h₂ : i in startingAt...s₁.vars.size do
      if s₁.vars[i] != s₂.vars[i]'(by have y := Std.PRange.lt_upper_of_mem h₂; simp_all +zetaDelta) then
        return false
    true
  else
    false

open TSyntax.Compat in
partial def collect (stx : Syntax) : M Syntax := withRef stx <| withFreshMacroScope do
  let k := stx.getKind
  if k == identKind then
    processId stx
  else if k == ``Lean.Parser.Term.app then
    processCtorApp stx
  else if k == ``Lean.Parser.Term.anonymousCtor then
    let elems ← stx[1].getArgs.mapSepElemsM collect
    return stx.setArg 1 <| mkNullNode elems
  else if k == ``Lean.Parser.Term.dotIdent then
    -- TODO: validate that `stx` corresponds to a valid constructor or match pattern
    return stx
  else if k == ``Lean.Parser.Term.hole then
    `(.( $stx ))
  else if k == ``Lean.Parser.Term.syntheticHole then
    `(.( $stx ))
  else if k == ``Lean.Parser.Term.typeAscription then
    -- Ignore type term
    let t := stx[1]
    let t ← collect t
    return stx.setArg 1 t
  else if k == ``Lean.Parser.Term.explicitUniv then
    processCtor stx[0]
  else if k == ``Lean.Parser.Term.explicit then
    processCtor stx
  else if k == ``Lean.Parser.Term.namedPattern then
    /- Recall that
      ```
      def namedPattern := check... >> trailing_parser "@" >> optional (atomic (ident >> ":")) >> termParser
      ```
     -/
    let id := stx[0]
    discard <| processVar id
    let h ← if stx[2].isNone then
      `(h)
    else
      pure stx[2][0]
    let pat := stx[3]
    let pat ← collect pat
    discard <| processVar h
    ``(_root_.namedPattern $id $pat $h)
  else if k == ``Lean.Parser.Term.binop then
    /-
    We support `binop%` syntax in patterns because we
    wanted to support `x+1` in patterns.
    Recall that the `binop%` syntax was added to improve elaboration of some binary operators: `+` is one of them.
    Recall that `HAdd.hAdd` is marked as `[match_pattern]`
    TODO for a distant future: make this whole procedure extensible.
    -/
    -- Check whether the `binop%` operator is marked with `[match_pattern]`,
    -- We must check that otherwise Lean will accept operators that are not tagged with this annotation.
    let some (.const fName _) ← resolveId? stx[1] "pattern"
      | throwCtorExpected none
    unless hasMatchPatternAttribute (← getEnv) fName do
      throwCtorExpected none
    let lhs ← collect stx[2]
    let rhs ← collect stx[3]
    return stx.setArg 2 lhs |>.setArg 3 rhs
  else if k == ``Lean.Parser.Term.unop then
    let arg ← collect stx[2]
    return stx.setArg 2 arg
  else if k == ``Lean.Parser.Term.inaccessible then
    return stx
  else if k == strLitKind then
    return stx
  else if k == numLitKind then
    return stx
  else if k == scientificLitKind then
    return stx
  else if k == charLitKind then
    return stx
  else if k == ``Lean.Parser.Term.quotedName || k == ``Lean.Parser.Term.doubleQuotedName then
    return stx
  else if k == choiceKind then
    /- Remark: If there are `Term.structInst` alternatives, we keep only them. This is a hack to get rid of
       Set-like notation in patterns. Recall that in Mathlib `{a, b}` can be a set with two elements or the
       structure instance `{ a := a, b := b }`. Possible alternative solution: add a `pattern` category, or at least register
       the `Syntax` node kinds that are allowed in patterns. -/
    let args :=
      let args := stx.getArgs
      if args.any (·.isOfKind ``Parser.Term.structInst) then
        args.filter (·.isOfKind ``Parser.Term.structInst)
      else
        args
    let stateSaved ← get
    let arg0 ← collect args[0]!
    let stateNew ← get
    let mut argsNew := #[arg0]
    for arg in args[1...*] do
      set stateSaved
      argsNew := argsNew.push (← collect arg)
      unless samePatternsVariables stateSaved.vars.size stateNew (← get) do
        throwError "Invalid pattern: Overloaded notation is only allowed when all alternatives have the same set of pattern variables"
    set stateNew
    return mkNode choiceKind argsNew
  else match stx with
  | `({ $[$srcs?,* with]? $fields,* $[..%$ell?]? $[: $ty?]? }) =>
    if let some srcs := srcs? then
      throwErrorAt (mkNullNode srcs) "Invalid struct instance pattern: `with` is not allowed in patterns"
    let fields ← fields.getElems.mapM fun
      | `(Parser.Term.structInstField| $lval:structInstLVal := $val) => do
        let newVal ← collect val
        `(Parser.Term.structInstField| $lval:structInstLVal := $newVal)
      | _ => throwInvalidPattern  -- `structInstField` should be expanded at this point
    `({ $[$srcs?,* with]? $fields,* $[..%$ell?]? $[: $ty?]? })
  | _ => throwInvalidPattern

where

  processCtorApp (stx : Syntax) : M Syntax := do
    let (f, namedArgs, args, ellipsis) ← expandApp stx
    if f.getKind == ``Parser.Term.dotIdent then
      let namedArgsNew ← namedArgs.mapM fun
        -- We must ensure that `ref[1]` remains original to allow named-argument hints
        | { ref, name, val := Arg.stx arg } => withRef ref do `(Lean.Parser.Term.namedArgument| ($(ref[1]) := $(← collect arg)))
        | _ => unreachable!
      let mut argsNew ← args.mapM fun | Arg.stx arg => collect arg | _ => unreachable!
      if ellipsis then
        argsNew := argsNew.push (mkNode ``Parser.Term.ellipsis #[mkAtomFrom stx ".."])
      return Syntax.mkApp f (namedArgsNew ++ argsNew)
    else
      processCtorAppCore f namedArgs args ellipsis

  processCtor (stx : Syntax) : M Syntax := do
    processCtorAppCore stx #[] #[] false

  /-- Check whether `stx` is a pattern variable or constructor-like (i.e., constructor or constant tagged with `[match_pattern]` attribute) -/
  processId (stx : Syntax) : M Syntax := do
    match (← resolveId? stx "pattern") with
    | none   => processVar stx
    | some f => match f with
      | Expr.const fName _ =>
        match (← getEnv).find? fName with
        | some (ConstantInfo.ctorInfo _) => processCtor stx
        | some _ =>
          if hasMatchPatternAttribute (← getEnv) fName then
            processCtor stx
          else
            processVar stx
        | none => throwCtorExpected (some stx)
      | _ => processVar stx

  pushNewArg (accessible : Bool) (ctx : Context) (arg : Arg) : M Context := do
    match arg with
    | Arg.stx stx =>
      let stx ← if accessible then collect stx else pure stx
      return { ctx with newArgs := ctx.newArgs.push stx }
    | _ => unreachable!

  processExplicitArg (accessible : Bool) (ctx : Context) : M Context := do
    match ctx.args with
    | [] =>
      if ctx.ellipsis then
        pushNewArg accessible ctx (Arg.stx (← `(_)))
      else
        throwWrongArgCount ctx false
    | arg::args =>
      pushNewArg accessible { ctx with args := args } arg

  processImplicitArg (accessible : Bool) (ctx : Context) : M Context := do
    if ctx.explicit then
      processExplicitArg accessible ctx
    else
      pushNewArg accessible ctx (Arg.stx (← `(_)))

  processCtorAppContext (ctx : Context) : M Syntax := do
    if isDone ctx then
      finalize ctx
    else
      let accessible := isNextArgAccessible ctx
      let (d, ctx)   := getNextParam ctx
      match ctx.namedArgs.findFinIdx? fun namedArg => namedArg.name == d.1 with
      | some idx =>
        let arg := ctx.namedArgs[idx]
        let ctx := { ctx with namedArgs := ctx.namedArgs.eraseIdx idx
                              usedNames := ctx.usedNames.insert arg.name }
        let ctx ← pushNewArg accessible ctx arg.val
        processCtorAppContext ctx
      | none =>
        let ctx ← match d.2 with
          | BinderInfo.implicit       => processImplicitArg accessible ctx
          | BinderInfo.strictImplicit => processImplicitArg accessible ctx
          | BinderInfo.instImplicit   => processImplicitArg accessible ctx
          | _                         => processExplicitArg accessible ctx
        processCtorAppContext ctx

  processCtorAppCore (f : Syntax) (namedArgs : Array NamedArg) (args : Array Arg) (ellipsis : Bool) : M Syntax := do
    let args := args.toList
    let (fId, explicit) ← match f with
      | `($fId:ident)  => pure (fId, false)
      | `(@$fId:ident) => pure (fId, true)
      | _              =>
        throwError "Invalid pattern: Expected an identifier in function position, but found{indentD f}"
    let some (Expr.const fName _) ← resolveId? fId "pattern" (withInfo := true) | throwCtorExpected (some fId)
    let fInfo ← getConstInfo fName
    let paramDecls ← forallTelescopeReducing fInfo.type fun xs _ => xs.mapM fun x => do
      let d ← getFVarLocalDecl x
      return (d.userName, d.binderInfo)
    match fInfo with
    | ConstantInfo.ctorInfo val =>
      processCtorAppContext
        { funId := fId, explicit := explicit, ctorVal? := val, paramDecls := paramDecls, namedArgs := namedArgs, args := args, ellipsis := ellipsis }
    | _ =>
      if hasMatchPatternAttribute (← getEnv) fName then
        processCtorAppContext
          { funId := fId, explicit := explicit, ctorVal? := none, paramDecls := paramDecls, namedArgs := namedArgs, args := args, ellipsis := ellipsis }
      else
        throwCtorExpected (some fId)

def main (alt : MatchAltView) : M MatchAltView := do
  let patterns ← alt.patterns.mapM fun p => do
    trace[Elab.match] "collecting variables at pattern: {p}"
    collect p
  return { alt with patterns := patterns }

end CollectPatternVars

/--
Collect pattern variables occurring in the `match`-alternative object views.
It also returns the updated views.
-/
def collectPatternVars (alt : MatchAltView) : TermElabM (Array PatternVar × MatchAltView) := do
  let (alt, s) ← (CollectPatternVars.main alt).run {}
  return (s.vars, alt)

/--
Return the pattern variables in the given pattern.
Remark: this method is not used by the main `match` elaborator, but in the precheck hook and other macros (e.g., at `Do.lean`).
-/
def getPatternVars (patternStx : Syntax) : TermElabM (Array PatternVar) := do
  let patternStx ← liftMacroM <| expandMacros patternStx
  let (_, s) ← (CollectPatternVars.collect patternStx).run {}
  return s.vars

/--
Return the pattern variables occurring in the given patterns.
This method is used in the `match` and `do` notation elaborators
-/
def getPatternsVars (patterns : Array Syntax) : TermElabM (Array PatternVar) := do
  let collect : CollectPatternVars.M Unit := do
    for pattern in patterns do
      discard <| CollectPatternVars.collect (← liftMacroM <| expandMacros pattern)
  let (_, s) ← collect.run {}
  return s.vars

def getPatternVarNames (pvars : Array PatternVar) : Array Name :=
  pvars.map fun x => x.getId

end Lean.Elab.Term
