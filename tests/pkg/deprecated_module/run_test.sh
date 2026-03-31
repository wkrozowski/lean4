rm -rf .lake/build

# Build Main library — includes all test modules
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
# (covered implicitly: if transitive warnings leaked, we'd see extra output)

# ConsumerIgnoreOne: "deprecated_module: ignore" on Old import only — OldNoMessage should still warn
check_out_contains "ConsumerIgnoreOne.lean:1:0: 'DeprecatedModule.OldNoMessage' has been deprecated"

# ConsumerShowDeprecated: #show_deprecated_modules should still list deprecated modules
# even when warnings are suppressed via "deprecated_module: ignore"
check_out_contains "ConsumerShowDeprecated.lean:6:0: Deprecated modules"
