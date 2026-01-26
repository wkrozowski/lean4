/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Pattern
public import Lean.Meta.DiscrTree
public import Lean.Meta.Eqns
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.Simp.DiscrTree
public section
namespace Lean.Meta.Sym.Simp


/-- Collection of simplification theorems available to the simplifier. -/
structure Theorems where
  thms : DiscrTree Theorem := {}

def Theorems.insert (thms : Theorems) (thm : Theorem) : Theorems :=
  { thms with thms := insertPattern thms.thms thm.pattern thm }

def Theorems.getMatch (thms : Theorems) (e : Expr) : Array Theorem :=
  Sym.getMatch thms.thms e

def Theorems.getMatchWithExtra (thms : Theorems) (e : Expr) : Array (Theorem × Nat) :=
  Sym.getMatchWithExtra thms.thms e

def mkTheoremFromDecl (declName : Name) : MetaM Theorem := do
  let (pattern, rhs) ← mkEqPatternFromDecl declName
  return { expr := mkConst declName, pattern, rhs }

def mkHEqTheoremFromDecl (declName : Name) : MetaM Theorem := do
  let (pattern, rhs) ← mkHEqPatternFromDecl declName
  return { expr := mkConst declName, pattern, rhs }

def mkTheoremsFromEquations (declName : Name) : MetaM <| Option Theorem := do
  let some eqn ← getUnfoldEqnFor? declName (nonRec := true) | return .none
  mkTheoremFromDecl eqn

def mkTheoremsFromEquations' (declName : Name) : MetaM <| Option Theorems := do
  let some eqns ← getEqnsFor? declName | return .none
  let mut thms : Theorems := {}
  for eqn in eqns do
    let thm ← mkTheoremFromDecl eqn
    thms := thms.insert thm
  return thms

end Lean.Meta.Sym.Simp
