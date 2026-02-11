/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.ScopedEnvExtension
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Sym.Simp.DiscrTree
import Lean.Meta.Sym.ProofInstInfo
import Lean.Meta.CollectMVars

public section
namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp
open Lean.Meta.Sym (insertPattern getMatchWithExtra preprocessType)
open DiscrTree (Key)

/-!
# CBV Simproc Extension

This module implements an extension system for registering simplification procedures (simprocs)
for the `cbv` tactic. Simprocs are arbitrary Lean functions (`Simproc = Expr → SimpM Result`)
that are triggered by pattern matching via SymM discrimination trees.

The architecture follows the same pattern as the regular `simp` simproc system
(`Lean.Meta.Tactic.Simp.Simproc`), adapted for the CBV/SymM infrastructure:

- **Builtin simprocs** are registered during initialization via `builtin_cbv_simproc_pattern%`
  and `@[builtin_cbv_simproc]`.
- **User-defined simprocs** are registered via `cbv_simproc_pattern%` and `@[cbv_simproc]`.
- Pattern matching uses SymM discrimination trees for efficient lookup.
-/

/-- Serializable entry for CBV simprocs (stored in .olean files). -/
structure CbvSimprocOLeanEntry where
  declName : Name
  post     : Bool := true
  keys     : Array Key := #[]
  deriving Inhabited

/-- Runtime entry for CBV simprocs (OLean entry + actual closure). -/
structure CbvSimprocEntry extends CbvSimprocOLeanEntry where
  proc : Simproc

instance : BEq CbvSimprocEntry where
  beq e₁ e₂ := e₁.declName == e₂.declName

instance : ToFormat CbvSimprocEntry where
  format e := format e.declName

/-- State of the CBV simproc extension: pre/post discrimination trees. -/
structure CbvSimprocs where
  pre          : DiscrTree CbvSimprocEntry := DiscrTree.empty
  post         : DiscrTree CbvSimprocEntry := DiscrTree.empty
  simprocNames : PHashSet Name := {}

instance : Inhabited CbvSimprocs := ⟨{}⟩

/-- Add a simproc entry to the extension state. -/
def CbvSimprocs.addCore (s : CbvSimprocs) (keys : Array Key) (declName : Name) (post : Bool) (proc : Simproc) : CbvSimprocs :=
  let entry : CbvSimprocEntry := { declName, keys, post, proc }
  let s := { s with simprocNames := s.simprocNames.insert declName }
  if post then
    { s with post := s.post.insertKeyValue keys entry }
  else
    { s with pre := s.pre.insertKeyValue keys entry }

/--
Builtin CBV simproc declarations.
Populated during initialization via `builtin_cbv_simproc_pattern%`.
-/
structure BuiltinCbvSimprocs where
  keys  : Std.HashMap Name (Array Key) := {}
  procs : Std.HashMap Name Simproc := {}

instance : Inhabited BuiltinCbvSimprocs := ⟨{}⟩

builtin_initialize builtinCbvSimprocDeclsRef : IO.Ref BuiltinCbvSimprocs ← IO.mkRef {}

/-- Builtin CBV simprocs state (pre-populated during initialization). -/
builtin_initialize builtinCbvSimprocsRef : IO.Ref CbvSimprocs ← IO.mkRef {}

/--
Register a builtin CBV simproc (keys + proc).
Can only be called during initialization.
-/
def registerBuiltinCbvSimprocCore (declName : Name) (keys : Array Key) (proc : Simproc) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError s!"Invalid builtin CBV simproc declaration: It can only be registered during initialization")
  if (← builtinCbvSimprocDeclsRef.get).keys.contains declName then
    throw (IO.userError s!"Invalid builtin CBV simproc declaration `{privateToUserName declName}`: already declared")
  builtinCbvSimprocDeclsRef.modify fun { keys := ks, procs } =>
    { keys := ks.insert declName keys, procs := procs.insert declName proc }

def registerBuiltinCbvSimproc (declName : Name) (keys : Array Key) (proc : Simproc) : IO Unit :=
  registerBuiltinCbvSimprocCore declName keys proc

/--
Persistent extension for tracking CBV simproc declarations and their keys.
This maps declaration names to their discrimination tree keys.
-/
structure CbvSimprocDecl where
  declName : Name
  keys     : Array Key
  deriving Inhabited

def CbvSimprocDecl.lt (d₁ d₂ : CbvSimprocDecl) : Bool :=
  Name.quickLt d₁.declName d₂.declName

structure CbvSimprocDeclExtState where
  builtin    : Std.HashMap Name (Array Key)
  newEntries : PHashMap Name (Array Key) := {}
  deriving Inhabited

builtin_initialize cbvSimprocDeclExt : PersistentEnvExtension CbvSimprocDecl CbvSimprocDecl CbvSimprocDeclExtState ←
  registerPersistentEnvExtension {
    mkInitial       := return { builtin := (← builtinCbvSimprocDeclsRef.get).keys }
    addImportedFn   := fun _ => return { builtin := (← builtinCbvSimprocDeclsRef.get).keys }
    addEntryFn      := fun s d => { s with newEntries := s.newEntries.insert d.declName d.keys }
    exportEntriesFn := fun s =>
      let result := s.newEntries.foldl (init := #[]) fun result declName keys => result.push { declName, keys }
      result.qsort CbvSimprocDecl.lt
  }

/-- Look up the discrimination tree keys for a CBV simproc declaration. -/
def getCbvSimprocDeclKeys? (declName : Name) : CoreM (Option (Array Key)) := do
  let env ← getEnv
  let keys? ← match env.getModuleIdxFor? declName with
    | some modIdx => do
      let some decl := (cbvSimprocDeclExt.getModuleEntries env modIdx).binSearch { declName, keys := #[] } CbvSimprocDecl.lt
        | pure none
      pure (some decl.keys)
    | none => pure ((cbvSimprocDeclExt.getState env).newEntries.find? declName)
  if let some keys := keys? then
    return some keys
  else
    return (cbvSimprocDeclExt.getState env).builtin[declName]?

def isCbvSimproc (declName : Name) : CoreM Bool :=
  return (← getCbvSimprocDeclKeys? declName).isSome

def isBuiltinCbvSimproc (declName : Name) : CoreM Bool := do
  let s := cbvSimprocDeclExt.getState (← getEnv)
  return s.builtin.contains declName

/-- Register a user-defined CBV simproc (keys only, proc loaded later). -/
def registerCbvSimproc (declName : Name) (keys : Array Key) : CoreM Unit := do
  let env ← getEnv
  unless (env.getModuleIdxFor? declName).isNone do
    throwError "Invalid CBV simproc declaration `{.ofConstName declName}`: declared in an imported module"
  if (← isCbvSimproc declName) then
    throwError "Invalid CBV simproc declaration `{.ofConstName declName}`: already declared"
  modifyEnv fun env => cbvSimprocDeclExt.modifyState env fun s =>
    { s with newEntries := s.newEntries.insert declName keys }

/-- Evaluate a declaration to obtain its `Simproc` closure. -/
unsafe def getCbvSimprocFromDeclImpl (declName : Name) : ImportM Simproc := do
  let ctx ← read
  match ctx.env.find? declName with
  | none => throw (IO.userError s!"Unknown constant `{declName}`")
  | some _info =>
    IO.ofExcept <| ctx.env.evalConst Simproc ctx.opts declName

@[implemented_by getCbvSimprocFromDeclImpl]
opaque getCbvSimprocFromDecl (declName : Name) : ImportM Simproc

def toCbvSimprocEntry (e : CbvSimprocOLeanEntry) : ImportM CbvSimprocEntry := do
  return { toCbvSimprocOLeanEntry := e, proc := (← getCbvSimprocFromDecl e.declName) }

/-- Scoped extension type for CBV simprocs. -/
abbrev CbvSimprocExtension := ScopedEnvExtension CbvSimprocOLeanEntry CbvSimprocEntry CbvSimprocs

builtin_initialize cbvSimprocExt : CbvSimprocExtension ←
  registerScopedEnvExtension {
    name         := `cbvSimprocExt
    mkInitial    := builtinCbvSimprocsRef.get
    ofOLeanEntry := fun _ => toCbvSimprocEntry
    toOLeanEntry := fun e => e.toCbvSimprocOLeanEntry
    addEntry     := fun s e => s.addCore e.keys e.declName e.post e.proc
  }

/-- Get the current CBV simproc state. -/
def getCbvSimprocs : CoreM CbvSimprocs :=
  return cbvSimprocExt.getState (← getEnv)

/-- Add a builtin CBV simproc to the builtin state (called during initialization). -/
def addCbvSimprocBuiltinAttr (declName : Name) (post : Bool) (proc : Simproc) : IO Unit := do
  let some keys := (← builtinCbvSimprocDeclsRef.get).keys[declName]? |
    throw (IO.userError s!"Invalid `[builtin_cbv_simproc]` attribute: `{privateToUserName declName}` is not a builtin CBV simproc")
  builtinCbvSimprocsRef.modify fun s => s.addCore keys declName post proc

/-- Add a CBV simproc attribute to a declaration. -/
def addCbvSimprocAttrCore (declName : Name) (kind : AttributeKind) (post : Bool) : CoreM Unit := do
  let proc ←
    try
      getCbvSimprocFromDecl declName
    catch e =>
      if (← isBuiltinCbvSimproc declName) then
        let some proc := (← builtinCbvSimprocDeclsRef.get).procs[declName]?
          | throwError "Invalid `[cbv_simproc]` attribute: `{.ofConstName declName}` is not a CBV simproc"
        pure proc
      else
        throw e
  let some keys ← getCbvSimprocDeclKeys? declName |
    throwError "Invalid `[cbv_simproc]` attribute: `{.ofConstName declName}` is not a CBV simproc"
  cbvSimprocExt.add { declName, post, keys, proc } kind

/--
Creates SymM DiscrTree keys from an elaborated pattern expression.

The expression may contain metavariables (from `_` in the pattern syntax),
which become wildcards (`Key.star`) in the discrimination tree.

The approach:
1. Instantiate assigned metavars
2. Preprocess (unfold reducible, beta/zeta/eta reduce) for SymM compatibility
3. Abstract remaining metavars to bvars (which become `Key.star` in the key sequence)
4. Generate keys via `Pattern.mkDiscrTreeKeys`
-/
def mkCbvSimprocKeys (patternExpr : Expr) : MetaM (Array Key) := do
  let patternExpr ← instantiateMVars patternExpr
  let patternExpr ← preprocessType patternExpr
  let mvarIds ← getMVars patternExpr
  let mvarExprs := mvarIds.map Expr.mvar
  let pattern := Expr.abstract patternExpr mvarExprs
  trace[Meta.Tactic] "pattern is : {pattern}"
  let p : Sym.Pattern := {
    levelParams := []
    varTypes := #[]
    pattern := pattern
    fnInfos := {}
    varInfos? := none
    checkTypeMask? := none
  }
  return p.mkDiscrTreeKeys

end Lean.Meta.Tactic.Cbv
