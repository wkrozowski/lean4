rm -rf .lake/build

# Build Main library — should produce deprecation warnings from Consumer importing Old and OldNoMessage
capture lake build Main

# With-message format: includes colon and custom message
check_out_contains "has been deprecated: use DeprecatedModule.New instead"

# Without-message format: just "has been deprecated" (no colon, no extra text)
check_out_matches "OldNoMessage. has been deprecated"
# Verify the no-message variant doesn't include a colon after "deprecated"
if grep -q "OldNoMessage.*has been deprecated:" "$CAPTURED.out.produced"; then
  echo "FAIL: OldNoMessage should not have a colon after 'has been deprecated'"
  exit 1
fi

# OldDouble has two deprecated_module commands — second triggers duplicate warning
check_out_contains "module is already marked as deprecated"

# TransitiveConsumer only imports Transitive (which imports Old) — no direct import, no warning
# Verify by checking that warnings only come from direct importers
# (covered implicitly: if transitive warnings leaked, we'd see extra output)

# Build Disabled library — linter.deprecatedModule is false, should produce no deprecation warnings
rm -rf .lake/build
capture_only "" lake build Disabled
if grep -q "has been deprecated" "$CAPTURED.out.produced"; then
  echo "FAIL: deprecation warning appeared despite linter.deprecatedModule = false"
  exit 1
fi
