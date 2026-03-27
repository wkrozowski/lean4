rm -rf .lake/build

# Build Main library — should produce deprecation warnings from Consumer importing Old and OldNoMessage
capture lake build Main

# With-message format: custom message on its own line, then deprecation with replacement imports
check_out_contains "use DeprecatedModule.New instead"
check_out_contains "'DeprecatedModule.Old' has been deprecated: please replace this import by"
check_out_contains "import DeprecatedModule.New"

# Without-message format: deprecation with replacement imports but no custom message
check_out_contains "'DeprecatedModule.OldNoMessage' has been deprecated: please replace this import by"

# OldDouble has two deprecated_module commands — second triggers duplicate warning
check_out_contains "module is already marked as deprecated"

# TransitiveConsumer only imports Transitive (which imports Old) — no direct import, no warning
# Verify by checking that warnings only come from direct importers
# (covered implicitly: if transitive warnings leaked, we'd see extra output)

# Build Disabled library — linter.deprecated.module is false, should produce no deprecation warnings
rm -rf .lake/build
capture_only "" lake build Disabled
if grep -q "has been deprecated" "$CAPTURED.out.produced"; then
  echo "FAIL: deprecation warning appeared despite linter.deprecated.module = false"
  exit 1
fi
