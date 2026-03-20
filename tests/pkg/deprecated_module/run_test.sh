rm -rf .lake/build

# Build Main library — Consumer.lean imports Old and OldNoMessage, should produce deprecation warnings
capture lake build Main
check_out_contains "has been deprecated"
check_out_contains "use DeprecatedModule.New instead"
check_out_contains "module is already marked as deprecated"

# TransitiveConsumer only imports Transitive (which imports Old) — no direct import warning

# Build Disabled library — linter.deprecatedModule is false, should produce no import-time deprecation warnings
rm -rf .lake/build
capture_only "" lake build Disabled
if grep -q "has been deprecated" "$CAPTURED.out.produced"; then
  echo "FAIL: deprecation warning appeared despite linter.deprecatedModule = false"
  exit 1
fi
