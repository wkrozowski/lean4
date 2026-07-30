import Lake
open Lake DSL

package cq

@[lint_driver]
script lintDriver args do
  IO.println s!"lint-driver: {args}"
  return 0

@[default_target]
lean_lib Quality
