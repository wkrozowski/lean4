import Lake
open System Lake DSL

package stateful_linter

-- No `Elab.async` override: the test files toggle `Elab.async` per command with `set_option ... in`,
-- exercising both the sync and async stateful-linter paths in one package.
@[default_target]
lean_lib LinterTest
