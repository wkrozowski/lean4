import Lake
open System Lake DSL

package stateful_linter_mode_switch

-- No `Elab.async` override: the test file toggles `Elab.async` per command with `set_option ... in`,
-- exercising both the sync and async stateful-linter paths and the transitions between them.
@[default_target]
lean_lib StatefulLinterModeSwitch
