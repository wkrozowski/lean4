module

public import Lean.Data.Options

public register_option linter.style.whitespace : Bool := {
  defValue := false
  descr := "enable the whitespace linter"
}

/--
warning: `linter.style.commandStart` is an option; deprecate it using the `deprecation?` field of its definition instead of the `[deprecated]` attribute
-/
#guard_msgs in
@[deprecated linter.style.whitespace (since := "2026-01-07")]
public register_option linter.style.commandStart : Bool := {
  defValue := false
  descr := "deprecated: use the `linter.style.whitespace` option instead"
}
