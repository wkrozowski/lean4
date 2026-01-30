import Lean
open Lean
open Lean.Meta
def dumbIdentity (n : Nat) : Nat :=
  match n with
  | .zero => 0
  | .succ n => dumbIdentity n + 1
  termination_by (n,0)

def mkSimpContext (config : Simp.Config := {}) : MetaM Simp.Context := do
  let s : SimpTheorems := {}
  let s ← s.addConst ``dumbIdentity.eq_1
  let s ← s.addConst ``dumbIdentity.eq_2
  let config := { config with implicitDefEqProofs := false, ground := true, arith := true}
  Simp.mkContext config #[s] {}

def createInstance (n : Nat) : Expr := .app (mkConst ``dumbIdentity) (mkNatLit n)

def runAndGetProof (e : Expr) : MetaM Expr := do
  let executed ← Lean.Meta.Tactic.Cbv.cbvEntry e
   match executed with
  | .rfl _ => throwError "didnt work"
  | .step _ proof _ => return proof

def runSingleTest (n : Nat) : MetaM Unit := do
  let toFeed := createInstance n
  let toFeedToMVar := mkNatEq toFeed (mkNatLit n)
  let mvar ← Meta.mkFreshExprMVar toFeedToMVar
  let startTime ← IO.monoNanosNow
  let proof ← runAndGetProof toFeed
  mvar.mvarId!.assign proof
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  let startTime ← IO.monoNanosNow
  Meta.checkWithKernel proof
  let endTime ← IO.monoNanosNow
  let kernelMs := (endTime - startTime).toFloat / 1000000.0
  IO.println s!"cbv: goal_{n}: {ms} ms, kernel: {kernelMs} ms"

def runSingleTestSimp (n : Nat) : MetaM Unit := do
  let toFeed := createInstance n
  let toFeed := mkNatEq toFeed (mkNatLit n)
  let mvar ← Meta.mkFreshExprMVar toFeed
  let mvar := mvar.mvarId!
  let context ← mkSimpContext
  let startTime ← IO.monoNanosNow
  let _ ← Lean.Meta.simpTargetCore mvar context
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  let proof ← instantiateMVars <| Expr.mvar mvar
  let startTime ← IO.monoNanosNow
  Meta.checkWithKernel proof
  let endTime ← IO.monoNanosNow
  let kernelMs := (endTime - startTime).toFloat / 1000000.0
  IO.println s!"simp: goal_{n}: {ms} ms, kernel: {kernelMs} ms"

theorem dumbIdentityThm : dumbIdentity 1 = 1 := by
  grind [dumbIdentity]

def runTests : MetaM Unit := do
  IO.println "=== Call-By-Value Tactic Tests ==="
  IO.println ""
  for n in [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150] do
    runSingleTest n
    runSingleTestSimp n

#eval runTests
