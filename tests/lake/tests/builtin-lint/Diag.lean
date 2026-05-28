import Linters

set_option linter.defProp true

def badNameExtra : Nat := 1

#eval show IO Unit from do
  let opts ← Lean.Linter.envLinterOptionsRef.get
  let names : Array Lean.Name := opts.map (fun o => o.name)
  IO.println s!"opts: {names}"

#eval show Lean.CoreM Unit from do
  let snap := Lean.Linter.EnvLinter.envLinterSnapshotExt.getState (← Lean.getEnv)
  IO.println s!"snapshot size: {snap.size}"
  match snap.find? `badNameExtra with
  | some entries => IO.println s!"badNameExtra entries: {entries.toArray}"
  | none => IO.println "no entries for badNameExtra"
