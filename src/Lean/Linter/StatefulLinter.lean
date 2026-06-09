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

/-!
# Stateful linters

A *stateful linter* carries a state of an arbitrary type `σ` that is folded across successive
top-level commands: for each command its `run` receives the previous command's state and produces the
new one. Stateful linters may also read *other* stateful linters' states — both the previous
command's (`LinterStateCtx.getPrev`) and the current command's (`LinterStateCtx.getCurr`) — blocking
until that state is available.

Each stateful linter runs on its own dedicated thread per command (see
`Lean.Elab.Command.runLintersAsync`), so a current-state read can block on another linter without
starving the elaboration thread pool. A *current-read cycle* (linter `A` reads `B`'s current state
and `B` reads `A`'s) is logically unsatisfiable and will deadlock that command's linting; avoiding
such cycles is the linter author's responsibility.

The type-erased machinery (`StatefulLinterState`, `LinterStateCtx`, `StatefulLinterStep`,
`statefulLintersRef`) lives in `Lean.Elab.Command`; this module provides the typed front end.
-/

namespace Lean.Linter

open Lean.Elab.Command (LinterStateCtx StatefulLinterState StatefulLinterStep CommandElabM
  statefulLintersRef)

/--
A handle to a registered stateful linter, used to read its state from another linter via
`LinterStateCtx.getPrev`/`getCurr`. `idx` is the linter's registration index; `init` is its initial
state, returned as the fallback when no state has been recorded yet. -/
structure StatefulLinterRef (σ : Type) where
  /-- The linter's registration index into `statefulLintersRef`. -/
  idx : Nat
  /-- The linter's initial state; the fallback when reading before any state has been recorded. -/
  init : σ
  deriving Nonempty

/--
A command linter that folds a state of type `σ` across top-level commands. For each command, `run`
receives the command syntax, this linter's state after the *previous* command (its `init` for the
first command), and a `LinterStateCtx` for reading other stateful linters' states; it returns the new
state. Register with `registerStatefulLinter`. -/
structure StatefulLinter (σ : Type) where
  /-- A name for the linter, used in traces and error messages. -/
  name : Name := by exact decl_name%
  /-- If set, the linter only folds when this option is enabled; otherwise its state is carried
  forward unchanged (but still made available to dependent linters). -/
  enableOpt? : Option (Lean.Option Bool) := none
  /-- The initial state, used before any command has run. -/
  init : σ
  /-- Folds the state over one command: `run stx prevState ctx` returns the new state. -/
  run : Syntax → σ → LinterStateCtx → CommandElabM σ

end Lean.Linter

namespace Lean.Elab.Command.LinterStateCtx

open Lean.Linter (StatefulLinterRef)

private unsafe def getPrevImpl {σ} (ctx : LinterStateCtx) (ref : StatefulLinterRef σ) : σ :=
  match ctx.prevTasks[ref.idx]? with
  | some t => unsafeCast t.get
  | none   => ref.init

/--
Reads the state of the stateful linter `ref` after the *previous* command, blocking until it is
available. Returns `ref.init` if `ref` has no state yet (e.g. on the first command). Because previous
states are always eventually resolved, this never deadlocks. -/
@[implemented_by getPrevImpl]
def getPrev {σ} (ctx : LinterStateCtx) (ref : StatefulLinterRef σ) : σ := ref.init

private unsafe def getCurrImpl {σ} (ctx : LinterStateCtx) (ref : StatefulLinterRef σ) : σ :=
  match ctx.currTasks[ref.idx]? with
  | some t => unsafeCast t.get
  | none   => ref.init

/--
Reads the state of the stateful linter `ref` for the *current* command, blocking until `ref` has
finished folding this command. Returns `ref.init` if `ref` is not registered. A cycle of current-state
reads is unsatisfiable and will deadlock; see the module doc. -/
@[implemented_by getCurrImpl]
def getCurr {σ} (ctx : LinterStateCtx) (ref : StatefulLinterRef σ) : σ := ref.init

end Lean.Elab.Command.LinterStateCtx

namespace Lean.Linter

open Lean.Elab.Command (StatefulLinterStep statefulLintersRef)

/--
Registers a stateful linter and returns a handle to it. Like `addLinter`, this may be called either
from an `initialize`/`builtin_initialize` block (the usual way, e.g. for a linter shipped in an
imported module) or imperatively during elaboration (e.g. `run_cmd`); in the latter case the linter
takes effect for subsequent commands.

Registration is keyed by `name`: registering a linter whose name is already registered updates that
linter in place and returns its existing index, rather than allocating a new one. This keeps indices
stable across re-elaboration (so the per-command state threaded in `Command.State.linterCursors`
stays aligned) and makes registration via `run_cmd` idempotent. -/
def registerStatefulLinter {σ : Type} [Nonempty σ] (l : StatefulLinter σ) :
    IO (StatefulLinterRef σ) := do
  let arr ← statefulLintersRef.get
  let step : StatefulLinterStep := {
    name       := l.name
    enableOpt? := l.enableOpt?
    -- safety: `StatefulLinterState` is opaque, so we can upcast `σ` to it
    init       := unsafe unsafeCast l.init
    run        := unsafe unsafeCast l.run
  }
  match arr.findIdx? (·.name == l.name) with
  | some idx =>
    statefulLintersRef.set (arr.set! idx step)
    return { idx, init := l.init }
  | none =>
    statefulLintersRef.set (arr.push step)
    return { idx := arr.size, init := l.init }

end Lean.Linter
