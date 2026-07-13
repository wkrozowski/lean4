import Lake
open System Lake DSL

package stateful_linter_error

-- No `Elab.async` override: the test file toggles `Elab.async` per command with `set_option ... in`,
-- so error handling is exercised on both the sync and async stateful-linter paths.
@[default_target]
lean_lib StatefulLinterError
