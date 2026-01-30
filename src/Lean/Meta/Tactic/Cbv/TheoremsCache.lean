/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude

public import Lean.Meta.Basic
public import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Eqns
import Lean.Meta.Match.MatchEqsExt

open Lean.Meta.Sym.Simp

namespace Lean.Meta.Tactic.Cbv

/--
Cache for CBV theorems. Stores three types of theorem mappings:
- `eqnTheorems`: Function equations from `getEqnsFor?`
- `unfoldTheorems`: Unfold equations from `getUnfoldEqnFor?`
- `matchTheorems`: Match equations from `Match.getEquationsFor`

The cache is session-local and not saved to .olean files.
-/
public structure CbvTheoremsCache where
  /-- Cache for function equations (from getEqnsFor?) -/
  eqnTheorems : PHashMap Name Theorems := {}
  /-- Cache for unfold equations (from getUnfoldEqnFor?) -/
  unfoldTheorems : PHashMap Name Theorem := {}
  /-- Cache for match equations (from Match.getEquationsFor) -/
  matchTheorems : PHashMap Name Theorems := {}
  /-- Holds names of functions that shouldnt be unfolded -/
  doNotUnfold : PHashSet Name := {}
  /-- Holds theorems registered by the user -/
  userTheorems : Theorems := {}
  deriving Inhabited

/--
Extension for caching CBV theorems. Uses `.local` async mode so theorems
are generated on demand and not saved to .olean files.
-/
builtin_initialize cbvTheoremsCacheExt : EnvExtension CbvTheoremsCache ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/--
Get or create cached Theorems for function equations.
Retrieves equations via `getEqnsFor?` and caches the resulting Theorems object.
-/
public def getEqnTheorems (fnName : Name) : MetaM Theorems := do
  let env ← getEnv
  let cache := cbvTheoremsCacheExt.getState env
  if let some thms := cache.eqnTheorems.find? fnName then
    return thms
  else
    -- Compute theorems from equation names
    let some eqnNames ← getEqnsFor? fnName | return {}
    let thms := Theorems.insertMany {} <| ← eqnNames.mapM mkTheoremFromDecl
    -- Store in cache
    modifyEnv fun env =>
      cbvTheoremsCacheExt.modifyState env fun cache =>
        { cache with eqnTheorems := cache.eqnTheorems.insert fnName thms }
    return thms

/--
Get or create cached Theorem for unfold equation.
Retrieves unfold equation via `getUnfoldEqnFor?` and caches the resulting Theorem.
-/
public def getUnfoldTheorem (fnName : Name) : MetaM (Option Theorem) := do
  let env ← getEnv
  let cache := cbvTheoremsCacheExt.getState env
  if let some thm := cache.unfoldTheorems.find? fnName then
    return some thm
  else
    -- Compute theorem from unfold equation
    let some unfoldEqn ← getUnfoldEqnFor? fnName (nonRec := true) | return none
    let thm ← mkTheoremFromDecl unfoldEqn
    -- Store in cache
    modifyEnv fun env =>
      cbvTheoremsCacheExt.modifyState env fun cache =>
        { cache with unfoldTheorems := cache.unfoldTheorems.insert fnName thm }
    return some thm

/--
Get or create cached Theorems for match equations.
Retrieves match equations via `Match.getEquationsFor` and caches the resulting Theorems object.
-/
public def getMatchTheorems (matcherName : Name) : MetaM Theorems := do
  let env ← getEnv
  let cache := cbvTheoremsCacheExt.getState env
  if let some thms := cache.matchTheorems.find? matcherName then
    return thms
  else
    -- Compute theorems from match equation names
    let eqns ← Match.getEquationsFor matcherName
    let thms := Theorems.insertMany {} <| ← eqns.eqnNames.mapM mkTheoremFromDecl
    -- Store in cache
    modifyEnv fun env =>
      cbvTheoremsCacheExt.modifyState env fun cache =>
        { cache with matchTheorems := cache.matchTheorems.insert matcherName thms }
    return thms

public def addDoNotUnfold (name : Name) : MetaM Unit := do
  modifyEnv fun env =>
      cbvTheoremsCacheExt.modifyState env fun cache =>
        { cache with doNotUnfold := cache.doNotUnfold.insert name }

public def getUserTheorems : MetaM Theorems := do
  let env ← getEnv
  let cache := cbvTheoremsCacheExt.getState env
  return cache.userTheorems

public def addUserTheoremFromDecl (name : Name) : MetaM Unit := do
  let thm ← mkTheoremFromDecl name
  modifyEnv fun env =>
      cbvTheoremsCacheExt.modifyState env fun cache =>
        { cache with userTheorems := cache.userTheorems.insert thm }

public def isForbidden (name : Name) : MetaM Bool := do
  let env ← getEnv
  let cache := cbvTheoremsCacheExt.getState env
  return cache.doNotUnfold.contains name

end Lean.Meta.Tactic.Cbv
