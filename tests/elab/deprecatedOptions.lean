/-!
This file tests deprecation warnings on options.
-/

-- Basic deprecation warning on a command-level set_option
/--
warning: `backward.eqns.deepRecursiveSplit` has been deprecated
-/
#guard_msgs in
set_option backward.eqns.deepRecursiveSplit true

/--
warning: `backward.eqns.nonrecursive` has been deprecated
-/
#guard_msgs in
set_option backward.eqns.nonrecursive true

-- set_option ... in should produce exactly ONE warning (not multiple)
/--
warning: `backward.eqns.nonrecursive` has been deprecated
-/
#guard_msgs in
set_option backward.eqns.nonrecursive true in
example := 0

-- Disabling linter.deprecated.options suppresses warnings
#guard_msgs in
set_option linter.deprecated.options false in
set_option backward.eqns.nonrecursive true

#guard_msgs in
set_option linter.deprecated.options false in
set_option backward.eqns.nonrecursive true in
example := 0

-- Disabling at command level also works
set_option linter.deprecated.options false

#guard_msgs in
set_option backward.eqns.nonrecursive true

#guard_msgs in
set_option backward.eqns.nonrecursive false in
example := 0
