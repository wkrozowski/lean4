import Lake
open System Lake DSL

package stateful_linter_async

-- No `Elab.async` override: this package exercises the asynchronous stateful-linter path.
@[default_target]
lean_lib StatefulLinterAsync
