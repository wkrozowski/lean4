/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Linter.Basic

public section

namespace Lean.Linter.StatefulLinter

open Lean.Elab.Command

structure StatefulLinterRef (σ : Type) where
  idx : Nat
  init : σ
  deriving Nonempty

structure StatefulLinter (σ : Type) where
  name : Name := by exact decl_name%
  init : σ
  run : Syntax → σ → StatefulLinterCtx → CommandElabM σ

private unsafe def getPrevImpl {σ} (ctx : StatefulLinterCtx) (ref : StatefulLinterRef σ) : σ :=
  match ctx.prevTasks[ref.idx]? with
  | some t => unsafeCast t.get
  | none   => ref.init

@[implemented_by getPrevImpl]
def getPrev {σ} (ctx : StatefulLinterCtx) (ref : StatefulLinterRef σ) : σ := ref.init

private unsafe def getCurrImpl {σ} (ctx : StatefulLinterCtx) (ref : StatefulLinterRef σ) : σ :=
  match ctx.currTasks[ref.idx]? with
  | some t => unsafeCast t.get
  | none   => ref.init

@[implemented_by getCurrImpl]
def getCurr {σ} (ctx : StatefulLinterCtx) (ref : StatefulLinterRef σ) : σ := ref.init

def registerStatefulLinter {σ : Type} [Nonempty σ] (l : StatefulLinter σ) : IO (StatefulLinterRef σ) := do
  unless (← initializing) do
    throw (IO.userError s!"failed to register stateful linter '{l.name}', \
      stateful linters can only be registered during initialization")
  let arr ← statefulLintersRef.get
  let idx := arr.size
  let step : StatefulLinterStep := {
    name := l.name
    init := unsafe unsafeCast l.init
    run  := unsafe unsafeCast l.run
  }
  statefulLintersRef.set (arr.push step)
    return { idx, init := l.init }

end Lean.Linter.StatefulLinter
