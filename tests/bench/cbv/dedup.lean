import Lean
import Std
open Lean
set_option cbv.warning false

def dedup (l : List Nat) : List Nat := Id.run do
  let mut S : Std.TreeSet Nat := ∅
  for i in l do
    S := S.insert i
  return S.toList

example : dedup [1] = [1] := by conv => lhs; cbv

example : dedup [1,2] = [1,2] := by conv => lhs; cbv

example : dedup [1,1] = [1] := by conv => lhs; cbv

theorem size_10 : dedup (List.range 10) = List.range 10 := by decide


def mkProblem (n : Nat) : Expr := mkApp (mkConst ``dedup) (mkApp (mkConst ``List.range) (mkNatLit n))

def runProblem (n : Nat) : MetaM Unit := do
  let problem := mkProblem n
  let startTime ← IO.monoNanosNow
  let executed ← Lean.Meta.Tactic.Cbv.cbvEntry problem
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  match executed with
  | .rfl _ => IO.println s!"goal_{n}: {ms} ms"
  | .step _ proof _ =>
    let startTime ← IO.monoNanosNow
    Meta.checkWithKernel proof
    let endTime ← IO.monoNanosNow
    let kernelMs := (endTime - startTime).toFloat / 1000000.0
    IO.println s!"cbv: goal_{n}: {ms} ms, kernel: {kernelMs} ms"

def runCbvTests : MetaM Unit := do
  IO.println "=== Call-By-Value Tactic Tests ==="
  IO.println ""
  for n in List.range 5 do
    runProblem n

#eval runProblem 1
#eval runProblem 2
#eval runProblem 3
#eval runProblem 4
#eval runProblem 5
#eval runProblem 10
#eval runProblem 15
#eval runProblem 20
#eval runProblem 25
#eval runProblem 30
