import Lean.Elab.Command

open Lean Elab Command

set_option trace.Elab.lint true

public meta def testModuleLinter : ModuleLinter where
  run := fun cmds => do
    throwError "stx: {cmds}"

run_cmd liftM (addModuleLinter testModuleLinter)
