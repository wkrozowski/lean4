import Lake
open System Lake DSL

package stateful_linter

-- The async stateful-linter path is not implemented yet, so build in synchronous mode.
@[default_target]
lean_lib StatefulLinterTest where
  leanOptions := #[⟨`Elab.async, false⟩]
